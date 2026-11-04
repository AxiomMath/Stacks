module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalChart
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityWitness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageWitness

/-!
# Lifting `g ∘ x'_{/T}` through an étale chart of `W`

In Situation 0GH8 let `ω : W₀ ⟶ W` be a representable étale morphism out of a Noetherian affine
formal algebraic space. In the proof of Stacks 0GI5 the formal component `x̂` of an element over a
limit factors through `ω`, and the algebra needs the composite `g ∘ x'_{k,/Z_k}` of a descended
witness to factor through `ω` as well. This file turns such factorizations into sections of an
étale morphism of algebraic spaces, which descend to a stage.

By Stacks 0ARB the base change `W₀ ×_{W, g} X'_{/T'} ⟶ X'_{/T'}` is the completion of a morphism
`ν : X̃ ⟶ X'` which is locally of finite type and an isomorphism over `U'`; it is étale by
Stacks 0AR4. For a morphism `y : Y ⟶ X'` of algebraic spaces, a section of `X̃ ×_{X'} Y ⟶ Y`
gives a lift `Y_{/|y|⁻¹T'} ⟶ W₀` of `g ∘ y_{/T'}`, and conversely by the full faithfulness of
Stacks 0GDR when `Y` is locally Noetherian.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.ChartAlgebraization`,
  `AlgebraicGeometry.Artin.ContractionSituation.nonempty_chartAlgebraization`: the morphism `ν`.
* `AlgebraicGeometry.Artin.ContractionSituation.ChartAlgebraization.liftOfSection`: the lift given
  by a section, with `liftOfSection_comp` and `completionSheafRestrict_liftOfSection`.
* `AlgebraicGeometry.Artin.ContractionSituation.ChartAlgebraization.exists_section_of_lift`: every
  lift comes from a section (Stacks 0GDR).
* `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_stage_lift`: the lift of
  `g ∘ y_{k,/Z_k}` at a stage of a stage witness, restricting to `x₀ ∘ p_{/Z}` over the limit.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

/-- `X'` is a locally Noetherian algebraic space. -/
theorem isLocallyNoetherian_X' : Space.IsLocallyNoetherian B S hS c.X' := fun W q hq =>
  (Space.exists_atlas_iff_forall_etale B S hS c.X' _ c.isAlgebraicSpace_X').mp
    c.hasEtaleLocalProperty_isLocallyNoetherian_X' W q
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).1 hq)

/-- **The algebraization of an étale chart of `W` pulled back to `X'_{/T'}`** (Stacks 0ARB and
0AR4). For a representable étale `ω : W₀ ⟶ W` there is an étale morphism `ν : X̃ ⟶ X'` of algebraic
spaces, an isomorphism over `U'`, whose completion along `T'` is the base change of `ω` along
`g`. -/
theorem exists_chartAlgebraization {W₀ : FormalSpace.FppfSheaf B S hS} (ω : W₀ ⟶ c.W)
    (hW₀ : FormalSpace.IsAffineFormalAlgebraicSpace B S hS W₀)
    (hω : FormalSpace.IsRepresentableEtale B S hS ω) :
    ∃ (Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Xt) (ν : Xt ⟶ c.X'),
      Space.IsEtale B S hS ν ∧
      IsIso (pullback.snd ν (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).ι) ∧
      ∃ ε : Space.completionSheaf B S hS Xt (Space.pointsMap B S hS Xt ν ⁻¹' c.T') ⟶
          pullback ω c.g,
        IsIso ε ∧ ε ≫ pullback.snd ω c.g = Space.completionSheafMap B S hS ν c.T' := by
  have hXsp := c.isAlgebraicSpace_X'
  have hXN := c.isLocallyNoetherian_X'
  have hCln := FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hXsp hXN
    c.T' c.isClosed_T'
  have hsnd : FormalSpace.IsRepresentableEtale B S hS (pullback.snd ω c.g) :=
    FormalSpace.isRepresentableEtale_pullback_snd B S hS ω c.g hω
  have hEf : FormalSpace.IsFormalAlgebraicSpace B S hS (pullback ω c.g) :=
    FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS ω c.g
      c.isLocallyNoetherian_W.1
      (FormalSpace.isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hW₀)
      (FormalSpace.isFormalAlgebraicSpace_completionSheaf_of_isClosed hXsp c.T' c.isClosed_T')
  have hEln : FormalSpace.IsLocallyNoetherian B S hS (pullback ω c.g) := by
    obtain ⟨-, I', Xi', f', haff', het', hsurj'⟩ := id hEf
    exact ⟨hEf, I', Xi', f', haff', het', hsurj', fun j =>
      FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hCln _
        (haff' j) (FormalSpace.IsRepresentableEtale.comp B S hS (het' j) hsnd)⟩
  let Eobj : FormalSpace.RigEtaleOverCompletion B S hS c.X' c.T' :=
    ⟨Over.mk (pullback.snd ω c.g), hEf, hEln,
      isRigEtale_of_isRepresentableEtale_of_isLocallyNoetherian _ hEln hCln hsnd⟩
  have := FormalSpace.isEquivalence_completionModificationFunctor c.T' c.isClosed_T' hXsp hXN
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (FormalSpace.completionModificationFunctor c.T' c.isClosed_T' hXsp hXN) Eobj
  let ν : M.obj.left ⟶ c.X' := M.obj.hom
  have hνU : IsIso (pullback.snd ν (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).ι) :=
    M.property.1.2
  let ε : Space.completionSheaf B S hS M.obj.left (Space.pointsMap B S hS _ ν ⁻¹' c.T') ⟶
      pullback ω c.g := e.hom.hom.left
  have hε : ε ≫ pullback.snd ω c.g = Space.completionSheafMap B S hS ν c.T' := Over.w e.hom.hom
  have : IsIso ε := by
    show IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso e).hom
    infer_instance
  have hνet : Space.IsEtale B S hS ν := by
    have hrep : FormalSpace.IsRepresentableEtale B S hS
        (Space.completionSheafMap B S hS ν c.T') := by
      rw [← hε]
      exact (FormalSpace.isRepresentableEtale_of_isIso B S hS ε).comp B S hS hsnd
    exact FormalSpace.isEtale_of_isEtale_completionSheafMap_space B S hS M.property.1.1 hXsp ν
      c.T' c.isClosed_T'
      (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hXsp hXN)
      M.property.2 (Space.isEtale_openComplementRestriction B S hS ν c.T' hνU) hrep
  exact ⟨M.obj.left, M.property.1.1, ν, hνet, hνU, ε, inferInstance, hε⟩

/-- **An algebraization of the base change of an étale chart `ω : W₀ ⟶ W` along `g`**: an
étale morphism `ν : X̃ ⟶ X'`, an isomorphism over `U'`, with an isomorphism `ε` over `X'_{/T'}`
from its completion to `W₀ ×_{W, g} X'_{/T'}`. -/
structure ChartAlgebraization {W₀ : FormalSpace.FppfSheaf B S hS} (ω : W₀ ⟶ c.W) where
  /-- The algebraic space `X̃`. -/
  Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  isAlgebraicSpace_Xt : IsAlgebraicSpace B S hS Xt
  /-- The morphism `ν : X̃ ⟶ X'`. -/
  ν : Xt ⟶ c.X'
  isEtale_ν : Space.IsEtale B S hS ν
  isIso_ν : IsIso (pullback.snd ν (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).ι)
  /-- The identification of the completion of `ν` with the base change of `ω`. -/
  ε : Space.completionSheaf B S hS Xt (Space.pointsMap B S hS Xt ν ⁻¹' c.T') ⟶ pullback ω c.g
  isIso_ε : IsIso ε
  ε_snd : ε ≫ pullback.snd ω c.g = Space.completionSheafMap B S hS ν c.T'

/-- An étale morphism `ω : W₀ ⟶ W` from an affine formal algebraic space admits an
algebraization of its base change along `g`. -/
theorem nonempty_chartAlgebraization {W₀ : FormalSpace.FppfSheaf B S hS} (ω : W₀ ⟶ c.W)
    (hW₀ : FormalSpace.IsAffineFormalAlgebraicSpace B S hS W₀)
    (hω : FormalSpace.IsRepresentableEtale B S hS ω) : Nonempty (ChartAlgebraization c ω) := by
  obtain ⟨Xt, hXt, ν, hν, hνU, ε, hε, hεs⟩ := c.exists_chartAlgebraization ω hW₀ hω
  exact ⟨⟨Xt, hXt, ν, hν, hνU, ε, hε, hεs⟩⟩

/-- Restricting completions along a transport of the source set. -/
theorem eqToHom_comp_completionSheafRestrict {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F' ⟶ F) {T₁ T₂ : Set (Space.points B S hS F')} (e : T₁ = T₂)
    (T : Set (Space.points B S hS F)) (h₂ : T₂ ⊆ Space.pointsMap B S hS F' f ⁻¹' T)
    (h₁ : T₁ ⊆ Space.pointsMap B S hS F' f ⁻¹' T) :
    eqToHom (congrArg (Space.completionSheaf B S hS F') e) ≫
        Space.completionSheafRestrict B S hS f T₂ T h₂ =
      Space.completionSheafRestrict B S hS f T₁ T h₁ := by
  subst e
  simp

/-- A section `σ` of `pullback.snd ν y` gives a lift `σ ≫ pullback.fst ν y` of `y` through `ν`. -/
private theorem section_comp_fst_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ν : X ⟶ Z}
    {y : Y ⟶ Z} (σ : Y ⟶ pullback ν y) (hσ : σ ≫ pullback.snd ν y = 𝟙 Y) :
    (σ ≫ pullback.fst ν y) ≫ ν = y := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

/-- If `a ≫ f = h`, a set mapping into the inverse image of `T₃` under `h` maps into the inverse
image under `a` of the inverse image of `T₃` under `f`. -/
private theorem subset_preimage_pointsMap_of_comp_eq {F₁ F₂ F₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F₁ ⟶ F₂) (f : F₂ ⟶ F₃) {h : F₁ ⟶ F₃} (e : a ≫ f = h)
    {T₁ : Set (Space.points B S hS F₁)} {T₃ : Set (Space.points B S hS F₃)}
    (hT : T₁ ⊆ Space.pointsMap B S hS F₁ h ⁻¹' T₃) :
    T₁ ⊆ Space.pointsMap B S hS F₁ a ⁻¹' (Space.pointsMap B S hS F₂ f ⁻¹' T₃) := by
  subst e
  intro x hx
  change Space.pointsMap B S hS _ f (Space.pointsMap B S hS _ a x) ∈ T₃
  rw [← Function.comp_apply (f := Space.pointsMap B S hS _ f), ← Space.pointsMap_comp]
  exact hT hx

namespace ChartAlgebraization

variable {c} {W₀ : FormalSpace.FppfSheaf B S hS} {ω : W₀ ⟶ c.W} (A : ChartAlgebraization c ω)

/-- A section `σ` of `X̃ ×_{X'} Y ⟶ Y` carries every point of `Y` over `T'` to a point of `X̃`
over `T'`. -/
theorem subset_preimage_of_section {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ c.X')
    {TY : Set (Space.points B S hS Y)} (hTY : TY ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y) :
    TY ⊆ Space.pointsMap B S hS Y (σ ≫ pullback.fst A.ν y) ⁻¹'
      (Space.pointsMap B S hS A.Xt A.ν ⁻¹' c.T') := by
  exact subset_preimage_pointsMap_of_comp_eq _ _ (section_comp_fst_comp σ hσ) hTY

/-- **The lift of `g ∘ y_{/T'}` given by a section** of `X̃ ×_{X'} Y ⟶ Y`. -/
noncomputable def liftOfSection {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ c.X')
    (TY : Set (Space.points B S hS Y)) (hTY : TY ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y) :
    Space.completionSheaf B S hS Y TY ⟶ W₀ :=
  Space.completionSheafRestrict B S hS (σ ≫ pullback.fst A.ν y) TY _
      (A.subset_preimage_of_section y hTY σ hσ) ≫ A.ε ≫ pullback.fst ω c.g

/-- The lift given by a section lifts `g ∘ y_{/T'}`. -/
theorem liftOfSection_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ c.X')
    (TY : Set (Space.points B S hS Y)) (hTY : TY ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y) :
    A.liftOfSection y TY hTY σ hσ ≫ ω =
      Space.completionSheafRestrict B S hS y TY c.T' hTY ≫ c.g := by
  have h := section_comp_fst_comp σ hσ
  simp only [liftOfSection, Category.assoc]
  rw [pullback.condition, reassoc_of% A.ε_snd,
    ← Space.completionSheafRestrict_self B S hS A.ν c.T' (fun _ h => h),
    ← Category.assoc, ← Space.completionSheafRestrict_comp B S hS _ A.ν TY _ c.T' _ (fun _ h => h)
      (fun x hx => by rw [h]; exact hTY hx)]
  exact congrArg (· ≫ c.g) (Space.completionSheafRestrict_congr B S hS h _ _ _ _)

/-- The lift given by a section is compatible with base change. -/
theorem completionSheafRestrict_liftOfSection {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (y : Y ⟶ c.X') (TY : Set (Space.points B S hS Y))
    (hTY : TY ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y)
    (a : Y' ⟶ Y) (TY' : Set (Space.points B S hS Y'))
    (hTY' : TY' ⊆ Space.pointsMap B S hS Y' a ⁻¹' TY) (y' : Y' ⟶ c.X')
    (hTY'' : TY' ⊆ Space.pointsMap B S hS Y' y' ⁻¹' c.T')
    (σ' : Y' ⟶ pullback A.ν y') (hσ' : σ' ≫ pullback.snd A.ν y' = 𝟙 Y')
    (hσσ' : σ' ≫ pullback.fst A.ν y' = a ≫ σ ≫ pullback.fst A.ν y) :
    Space.completionSheafRestrict B S hS a TY' TY hTY' ≫ A.liftOfSection y TY hTY σ hσ =
      A.liftOfSection y' TY' hTY'' σ' hσ' := by
  simp only [liftOfSection]
  rw [← Category.assoc, ← Space.completionSheafRestrict_comp B S hS a (σ ≫ pullback.fst A.ν y) TY'
    TY _ hTY' (A.subset_preimage_of_section y hTY σ hσ)
    (fun x hx => by rw [← hσσ']; exact A.subset_preimage_of_section y' hTY'' σ' hσ' hx)]
  exact congrArg (· ≫ A.ε ≫ pullback.fst ω c.g)
    (Space.completionSheafRestrict_congr B S hS hσσ'.symm _ _ _ _)

/-- **A lift of `g ∘ y_{/T'}` comes from a section** (Stacks 0GDR). For a locally Noetherian
algebraic space `Y` and `y : Y ⟶ X'`, every morphism `ℓ : Y_{/|y|⁻¹T'} ⟶ W₀` lifting
`g ∘ y_{/T'}` through `ω` is the lift given by a section of `X̃ ×_{X'} Y ⟶ Y`: that morphism is
étale and an isomorphism over `Y ∖ |y|⁻¹T'`, and `ℓ` is a section of its completion. -/
theorem exists_section_of_lift {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (y : Y ⟶ c.X') (ℓ : Space.completionSheaf B S hS Y (Space.pointsMap B S hS Y y ⁻¹' c.T') ⟶ W₀)
    (hℓ : ℓ ≫ ω = Space.completionSheafRestrict B S hS y _ c.T' (fun _ h => h) ≫ c.g) :
    ∃ (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y),
      A.liftOfSection y _ (fun _ h => h) σ hσ = ℓ := by
  classical
  have := A.isIso_ν
  have := A.isIso_ε
  let T : Set (Space.points B S hS Y) := Space.pointsMap B S hS Y y ⁻¹' c.T'
  have hT : IsClosed T := c.isClosed_T'.preimage (Space.continuous_pointsMap B S hS y)
  let f := pullback.snd A.ν y
  have hP : IsAlgebraicSpace B S hS (pullback A.ν y) :=
    isAlgebraicSpace_pullback B S hS A.ν y A.isAlgebraicSpace_Xt hY c.isAlgebraicSpace_X'
  have hfet : Space.IsEtale B S hS f :=
    Space.isEtale_pullback_snd B S hS hY c.isAlgebraicSpace_X' A.isAlgebraicSpace_Xt A.ν y
      A.isEtale_ν
  have hflft : Space.IsLocallyOfFiniteType B S hS f :=
    Space.isLocallyOfFiniteType_of_isEtale' B S hS f hfet
  have hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS Y Tᶜ).ι) :=
    Space.isIso_pullback_snd_pullback_snd_openSubspaceOfPoints B S hS A.ν y
  have hbij := Space.completionOverFunctor_map_bijective hY hYN hT hP hflft hfU (𝟙 Y) hY hYN
  -- the formal section
  let TX := Space.pointsMap B S hS A.Xt A.ν ⁻¹' c.T'
  let TP := Space.pointsMap B S hS _ f ⁻¹' T
  have hTP : TP = Space.pointsMap B S hS _ (pullback.fst A.ν y) ⁻¹' TX :=
    (Space.preimage_pointsMap_eq_of_comm B S hS pullback.condition c.T').symm
  have sq := Space.isPullback_completionSheafRestrict B S hS (pullback.fst A.ν y) f A.ν y
    (IsPullback.of_hasPullback A.ν y) c.T' TP TX T rfl rfl hTP
    hTP.subset (fun _ h => h) (fun _ h => h) (fun _ h => h)
  let m : Space.completionSheaf B S hS Y T ⟶ Space.completionSheaf B S hS A.Xt TX :=
    pullback.lift ℓ (Space.completionSheafRestrict B S hS y T c.T' (fun _ h => h)) hℓ ≫ inv A.ε
  have hm : m ≫ Space.completionSheafRestrict B S hS A.ν TX c.T' (fun _ h => h) =
      𝟙 _ ≫ Space.completionSheafRestrict B S hS y T c.T' (fun _ h => h) := by
    have hr : Space.completionSheafRestrict B S hS A.ν TX c.T' (fun _ h => h) =
        Space.completionSheafMap B S hS A.ν c.T' :=
      Space.completionSheafRestrict_self B S hS A.ν c.T' _
    rw [hr, ← A.ε_snd, Category.id_comp]
    simp only [m, Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _
  let s := sq.lift m (𝟙 _) hm
  have hs₁ : s ≫ Space.completionSheafRestrict B S hS (pullback.fst A.ν y) TP TX hTP.subset = m :=
    sq.lift_fst _ _ _
  have hs₂ : s ≫ Space.completionSheafRestrict B S hS f TP T (fun _ h => h) = 𝟙 _ :=
    sq.lift_snd _ _ _
  let T₁ := Space.pointsMap B S hS Y (𝟙 Y) ⁻¹' T
  have hT₀ : T ⊆ Space.pointsMap B S hS Y (𝟙 Y) ⁻¹' T := fun x hx => by
    show Space.pointsMap B S hS Y (𝟙 Y) x ∈ T
    rw [Space.pointsMap_id]
    exact hx
  have hT₁ : T ⊆ Space.pointsMap B S hS Y (𝟙 Y) ⁻¹' T₁ :=
    subset_preimage_pointsMap_of_comp_eq _ _ (Category.id_comp _) hT₀
  have hT₂ : T₁ ⊆ Space.pointsMap B S hS Y (𝟙 Y) ⁻¹' T := fun _ h => h
  let s' : (Space.completionOverFunctor B S hS T).obj (Over.mk (𝟙 Y)) ⟶
      (Space.completionOverFunctor B S hS T).obj (Over.mk f) :=
    Over.homMk (Space.completionSheafRestrict B S hS (𝟙 Y) T₁ T hT₂ ≫ s) (by
      show (Space.completionSheafRestrict B S hS (𝟙 Y) T₁ T hT₂ ≫ s) ≫
          Space.completionSheafMap B S hS f T = Space.completionSheafMap B S hS (𝟙 Y) T
      rw [← Space.completionSheafRestrict_self B S hS f T (fun _ h => h), Category.assoc, hs₂,
        Category.comp_id]
      rfl)
  obtain ⟨a, ha⟩ := hbij.2 s'
  have hσ : a.left ≫ f = 𝟙 Y := Over.w a
  have hsub₁ : T₁ ⊆ Space.pointsMap B S hS Y a.left ⁻¹' TP :=
    subset_preimage_pointsMap_of_comp_eq _ _ hσ fun _ h => h
  have hal : Space.completionSheafRestrict B S hS a.left T₁ TP hsub₁ =
      Space.completionSheafRestrict B S hS (𝟙 Y) T₁ T hT₂ ≫ s :=
    (FormalSpace.completionOverMap_eq_completionSheafRestrict T a hsub₁).symm.trans
      (congrArg (fun φ => φ.left) ha)
  have hsub : T ⊆ Space.pointsMap B S hS Y a.left ⁻¹' TP :=
    subset_preimage_pointsMap_of_comp_eq _ _ hσ hT₀
  have e1 : Space.completionSheafRestrict B S hS (𝟙 Y) T T₁ hT₁ ≫
      Space.completionSheafRestrict B S hS a.left T₁ TP hsub₁ =
        Space.completionSheafRestrict B S hS a.left T TP hsub :=
    (Space.completionSheafRestrict_comp B S hS (𝟙 Y) a.left T T₁ TP hT₁ hsub₁
      (by rwa [Category.id_comp])).symm.trans
      (Space.completionSheafRestrict_congr B S hS (Category.id_comp _) _ _ _ _)
  have hs : Space.completionSheafRestrict B S hS a.left T TP hsub = s := by
    rw [← e1, hal, ← Category.assoc, Space.completionSheafRestrict_id_comp,
      Space.completionSheafRestrict_id, Category.id_comp]
  refine ⟨a.left, hσ, ?_⟩
  simp only [liftOfSection]
  rw [Space.completionSheafRestrict_comp B S hS a.left (pullback.fst A.ν y) T TP TX hsub
    hTP.subset, hs]
  exact (congrArg (· ≫ A.ε ≫ pullback.fst ω c.g) hs₁).trans (by
    simp only [m, Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _)

/-- `AlgebraicGeometry.Artin.ContractionSituation.ChartAlgebraization.exists_section_of_lift`
for a closed set given as `|y|⁻¹T'` up to equality. -/
theorem exists_section_of_lift' {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (y : Y ⟶ c.X') {TY : Set (Space.points B S hS Y)}
    (hTY : TY = Space.pointsMap B S hS Y y ⁻¹' c.T')
    (ℓ : Space.completionSheaf B S hS Y TY ⟶ W₀)
    (hℓ : ℓ ≫ ω = Space.completionSheafRestrict B S hS y TY c.T' (hTY ▸ fun _ h => h) ≫ c.g) :
    ∃ (σ : Y ⟶ pullback A.ν y) (hσ : σ ≫ pullback.snd A.ν y = 𝟙 Y),
      A.liftOfSection y TY (hTY ▸ fun _ h => h) σ hσ = ℓ := by
  subst hTY
  exact A.exists_section_of_lift hY hYN y ℓ hℓ

end ChartAlgebraization

/-! ### Descending the lift to a stage -/

section Descent

variable {W₀ : FormalSpace.FppfSheaf B S hS} {ω : W₀ ⟶ c.W} (A : ChartAlgebraization c ω)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D} (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
  (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))
  {ξ : Triple c κ.pt.obj} {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat}

include hκ hD hpt in
/-- **A morphism `V' ⟶ X̃` over `X'` descends to a stage of a model.** For a model
`q : Y ⟶ V_j` of the witness with `y : Y ⟶ X'` restricting to `x'`, a morphism `s : V' ⟶ X̃` with
`ν ∘ s = x'` comes from `s_k : Y_k ⟶ X̃` with `ν ∘ s_k = y_k` at a later stage
(`AlgebraicGeometry.Space.exists_stage_hom_restricting_of_isLimit` for
`(s, p) : V' ⟶ X̃ × V_j` over `V_j`, compatibly with the maps to the limit preserving `X'`). -/
theorem exists_stage_hom_Xt {j : I} (M : StageModel c κ ξ w j) (y : M.Y ⟶ c.X')
    (hy : M.a ≫ y = w.x') (s : w.V' ⟶ A.Xt) (hs : s ≫ A.ν = w.x') :
    ∃ (k : I) (g : k ⟶ j) (sk : (M.baseChange g).Y ⟶ A.Xt),
      sk ≫ A.ν = M.baseChangeHom g ≫ y ∧ (M.baseChange g).a ≫ sk = s := by
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  have hT := Space.isAlgebraicSpace_terminal B S hS
  have hX'lp : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) c.X' :=
    Space.limitPreserving_of_isLocallyOfFiniteType B S hS c.isAlgebraicSpace_X'
      c.isLocallyOfFiniteType_X'
  have hXtft : Space.IsLocallyOfFiniteType B S hS (terminal.from A.Xt) := by
    rw [show terminal.from A.Xt = A.ν ≫ terminal.from c.X' from terminal.hom_ext _ _]
    exact Space.isLocallyOfFiniteType_comp' B S hS _ _ c.isAlgebraicSpace_X' hT
      (Space.isLocallyOfFiniteType_of_isEtale' B S hS A.ν A.isEtale_ν) c.isLocallyOfFiniteType_X'
  have hXtfp := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS
    A.isAlgebraicSpace_Xt).2 (Space.limitPreserving_of_isLocallyOfFiniteType B S hS
      A.isAlgebraicSpace_Xt hXtft)
  let V := (D.obj j).obj
  have hY₂ : IsAlgebraicSpace B S hS
      (pullback (terminal.from A.Xt) (terminal.from (yoneda.obj V))) :=
    isAlgebraicSpace_pullback B S hS _ _ A.isAlgebraicSpace_Xt (isAlgebraicSpace_yoneda B S hS _)
      hT
  have hp₂ : Space.IsLocallyOfFinitePresentation B S hS
      (pullback.snd (terminal.from A.Xt) (terminal.from (yoneda.obj V))) :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (Space.isPullback_homMk B S hS A.isAlgebraicSpace_Xt (isAlgebraicSpace_yoneda B S hS _) hT
        hY₂ (IsPullback.of_hasPullback _ _)) hXtfp
  let eV := M.isPullback_a.isoPullback
  let a : pullback (yoneda.map (κ.π.app j).hom) M.q ⟶
      pullback (terminal.from A.Xt) (terminal.from (yoneda.obj V)) :=
    eV.inv ≫ pullback.lift s (w.p ≫ yoneda.map (κ.π.app j).hom) (terminal.hom_ext _ _)
  obtain ⟨k, a', -, h2, h3⟩ := Space.exists_stage_hom_restricting_of_isLimit
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt j
    M.isAlgebraicSpace_Y hY₂ c.isAlgebraicSpace_X'.isSheaf hX'lp M.q M.isProper_q _ hp₂ y
    (pullback.fst _ _ ≫ A.ν) a (by
      simp only [a, eV, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
      rfl) (by
      simp only [a, eV, Category.assoc]
      rw [pullback.lift_fst_assoc, hs, ← hy, ← Category.assoc, IsPullback.isoPullback_inv_snd]
      rfl)
  let a'' : (M.baseChange k.hom).Y ⟶
      pullback (terminal.from A.Xt) (terminal.from (yoneda.obj V)) := a'
  have h3'' : pullback.lift
      (pullback.fst (yoneda.map (κ.π.app j).hom) M.q ≫ yoneda.map (κ.π.app k.left).hom)
      (pullback.snd (yoneda.map (κ.π.app j).hom) M.q) (by
        rw [Category.assoc, ← Functor.map_comp, cone_π_hom_comp, pullback.condition]) ≫ a'' =
      a := h3
  have hak : (M.baseChange k.hom).a ≫ a'' = eV.hom ≫ a := by
    rw [← h3'', ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · show pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
        IsPullback.isoPullback_hom_fst]
    · show pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  refine ⟨k.left, k.hom, a'' ≫ pullback.fst _ _, (Category.assoc _ _ _).trans h2, ?_⟩
  rw [← Category.assoc, hak]
  simp only [a, eV, Iso.hom_inv_id_assoc]
  rw [pullback.lift_fst]

/-- The completion `x̂'` of a witness is the restriction of `x'` to the completions. -/
theorem CompatibilityWitness.xhat'_eq_completionSheafRestrict {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (w : CompatibilityWitness c V Z u xhat) :
    w.xhat' = Space.completionSheafRestrict B S hS w.x' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)
      c.T' (w.preimage_p_eq_preimage_x').subset := by
  have := Space.mono_completionSheafInclusion B S hS c.X' c.T'
  rw [← cancel_mono (Space.completionSheafInclusion B S hS c.X' c.T'),
    Space.completionSheafRestrict_comp_inclusion]
  exact w.completion_x'.symm

omit [IsCofiltered I] in
/-- Points of `V'` over `Z` map into the inverse image of `Z_j` in a model. -/
theorem StageModel.subset_preimage_preimage {j : I} (M : StageModel c κ ξ w j) :
    Space.pointsMap B S hS w.V' w.p ⁻¹' ξ.Z ⊆
      Space.pointsMap B S hS w.V' M.a ⁻¹' (Space.pointsMap B S hS M.Y M.q ⁻¹' M.Z) := by
  refine subset_preimage_pointsMap_of_comp_eq M.a M.q M.isPullback_a.w.symm fun x hx => ?_
  rw [Set.mem_preimage, Space.pointsMap_comp, Function.comp_apply]
  exact M.subset_preimage_Z hx

include hκ hD hpt A in
/-- **The lift of `g ∘ x'_{k,/Z_k}` through the chart `ω` at a stage.** Let `ξ` be an element over
the limit whose formal component factors as `x̂ = ω ∘ x₀`, and `W` a stage witness of a witness `w`
of `ξ`. At a later stage `k` there is `ℓ : Y_{k,/Z_k} ⟶ W₀` with `ω ∘ ℓ = g ∘ y_{k,/T'}`
restricting over the limit to `x₀ ∘ p_{/Z}`. -/
theorem StageWitness.exists_stage_lift {j : I} (W : StageWitness c κ ξ w j)
    {x₀ : Space.completionSheaf B S hS (yoneda.obj κ.pt.obj) ξ.Z ⟶ W₀} (hx₀ : x₀ ≫ ω = ξ.xhat) :
    ∃ (k : I) (g : k ⟶ j) (ℓ : Space.completionSheaf B S hS (W.baseChange g).Y
        (Space.pointsMap B S hS _ (W.baseChange g).q ⁻¹' (W.baseChange g).Z) ⟶ W₀),
      ℓ ≫ ω = Space.completionSheafRestrict B S hS (W.baseChange g).y _ c.T'
          (W.baseChange g).subset_T' ≫ c.g ∧
        Space.completionSheafRestrict B S hS (W.baseChange g).a _ _
            ((W.baseChange g).subset_preimage_preimage) ≫ ℓ =
          Space.completionSheafRestrict B S hS w.p _ ξ.Z (fun _ h => h) ≫ x₀ := by
  have hVN := κ.pt.property
  have hV'N : Space.HasEtaleLocalProperty B S hS w.V'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS w.isAlgebraicSpace_V'
      (isAlgebraicSpace_yoneda B S hS _) w.p w.isProper_p.2.1.1
      (Space.hasEtaleLocalProperty_isLocallyNoetherian_yoneda hVN)
  let TY := Space.pointsMap B S hS w.V' w.p ⁻¹' ξ.Z
  have hTY : TY = Space.pointsMap B S hS w.V' w.x' ⁻¹' c.T' := w.preimage_p_eq_preimage_x'
  let ℓ' := Space.completionSheafRestrict B S hS w.p TY ξ.Z (fun _ h => h) ≫ x₀
  have hℓ' : ℓ' ≫ ω = Space.completionSheafRestrict B S hS w.x' TY c.T'
      (hTY ▸ fun _ h => h) ≫ c.g := by
    simp only [ℓ', Category.assoc, hx₀]
    rw [w.isPullback_xhat'.w, w.xhat'_eq_completionSheafRestrict c]
  obtain ⟨σ', hσ', hlift⟩ := A.exists_section_of_lift' w.isAlgebraicSpace_V' hV'N w.x' hTY ℓ' hℓ'
  let s := σ' ≫ pullback.fst A.ν w.x'
  have hs : s ≫ A.ν = w.x' := section_comp_fst_comp σ' hσ'
  obtain ⟨k, g, sk, hsk₁, hsk₂⟩ :=
    exists_stage_hom_Xt c A hκ hD hpt W.toStageModel W.y W.a_y s hs
  let W' := W.baseChange g
  have hsk₁' : sk ≫ A.ν = 𝟙 _ ≫ W'.y := by
    rw [hsk₁, Category.id_comp]
    rfl
  let σk : W'.Y ⟶ pullback A.ν W'.y := pullback.lift sk (𝟙 _) hsk₁'
  have hσk : σk ≫ pullback.snd A.ν W'.y = 𝟙 _ := pullback.lift_snd _ _ _
  refine ⟨k, g, A.liftOfSection W'.y _ W'.subset_T' σk hσk,
    A.liftOfSection_comp W'.y _ W'.subset_T' σk hσk, ?_⟩
  refine (A.completionSheafRestrict_liftOfSection W'.y _ W'.subset_T' σk hσk W'.a TY
    W'.subset_preimage_preimage w.x' (hTY ▸ fun _ h => h) σ' hσ' ?_).trans hlift
  have hσkf : σk ≫ pullback.fst A.ν W'.y = sk := pullback.lift_fst _ _ _
  show s = W'.a ≫ σk ≫ pullback.fst A.ν W'.y
  rw [hσkf]
  exact hsk₂.symm

end Descent

end AlgebraicGeometry.Artin.ContractionSituation

end
