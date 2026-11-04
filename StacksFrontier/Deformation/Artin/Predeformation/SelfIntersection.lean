module

public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation

/-!
# The predeformation category of a self-intersection

Let `Φ : 𝒳 ⟶ 𝒴` be a `1`-morphism of categories fibred in groupoids over the big fppf site of
`S` satisfying (RS), let `x₀` be an object of `𝒳` over `Spec k`, and let `w₀ = (x₀, x₀, id)` be
the diagonal object of the self-intersection `𝒲 = 𝒳 ×_{Φ, 𝒴, Φ} 𝒳`. By Stacks 07WL the
predeformation category `𝓕_{𝒲,k,w₀}` is the 2-fibre product of `𝓕_{𝒳,k,x₀}` with itself over
`𝓕_{𝒴,k,Φ(x₀)}`; this file records it as an equivalence over `𝒞_Λ` with the 2-fibre product
formed with the functor induced by `Φ` on both legs. (The right leg of Stacks 07WL is the functor
induced by `Φ` transported along `ψ(w₀)`, which is the identity at the diagonal object.)

## Main results

* `Deformation.Artin.selfIntersectionPredeformationEquivalence`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

universe u u₁ v₁ u₂ v₂

namespace Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}

section Transport

variable {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {iΛ : Spec (.of Λ) ⟶ S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The reversed arrow of an `eqToHom` of a predeformation category is an `eqToHom`. -/
theorem predeformation_morphisms_eqToHom_arrow
    {a b : (predeformationCategory iΛ q x₀ hx₀).carrier} (h : a = b) :
    letI := (predeformationCategory iΛ q x₀ hx₀).category
    ((predeformationCategory iΛ q x₀ hx₀).morphisms a b (eqToHom h)).arrow =
      eqToHom
        (congrArg (fun c => ((predeformationCategory iΛ q x₀ hx₀).objects c).point) h).symm := by
  let := (predeformationCategory iΛ q x₀ hx₀).category
  subst h
  rw [eqToHom_refl, eqToHom_refl]
  exact (predeformationCategory iΛ q x₀ hx₀).reversed_identity a

/-- The reversed arrow of a composite with `eqToHom`s on both sides. -/
theorem predeformation_morphisms_conj_arrow
    {a a' b b' : (predeformationCategory iΛ q x₀ hx₀).carrier} (h₁ : a = a') (h₂ : b' = b)
    (m : letI := (predeformationCategory iΛ q x₀ hx₀).category; a' ⟶ b') :
    letI := (predeformationCategory iΛ q x₀ hx₀).category
    ((predeformationCategory iΛ q x₀ hx₀).morphisms a b (eqToHom h₁ ≫ m ≫ eqToHom h₂)).arrow =
      eqToHom (congrArg (fun c => ((predeformationCategory iΛ q x₀ hx₀).objects c).point) h₂.symm) ≫
        ((predeformationCategory iΛ q x₀ hx₀).morphisms a' b' m).arrow ≫
          eqToHom (congrArg
            (fun c => ((predeformationCategory iΛ q x₀ hx₀).objects c).point) h₁.symm) := by
  let := (predeformationCategory iΛ q x₀ hx₀).category
  subst h₁ h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end Transport

section Uniqueness

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] {qX : X ⥤ Over S}
  {qY : Y ⥤ Over S} {iΛ : Spec (.of Λ) ⟶ S} {F : X ⥤ Y} {hF : F ⋙ qY = qX} {x₀ : X}
  {hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- An induced functor of predeformation categories is unique: it is determined by its
compatibility with the projections and its values on points, arrows and reversed arrows. -/
theorem InducedPredeformationFunctor.toFunctor_eq
    (G G' : InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀) : G.toFunctor = G'.toFunctor := by
  let DY := predeformationCategory iΛ qY (F.obj x₀) (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)
  let := (predeformationCategory iΛ qX x₀ hx₀).category
  let := DY.category
  have hobj : ∀ c, G.toFunctor.obj c = G'.toFunctor.obj c := by
    intro c
    apply DY.objects.injective
    refine deformationObject_ext_of_arrow ((DY.object_projection _).symm.trans
      ((Functor.congr_obj G.projection_comm c).trans
        ((Functor.congr_obj G'.projection_comm c).symm.trans (DY.object_projection _))))
      ((G.object_point c).trans (G'.object_point c).symm) ?_
    rw [G.object_arrow c, G'.object_arrow c]
    simp only [Category.assoc, eqToHom_trans]
  refine CategoryTheory.Functor.ext hobj fun c d f => ?_
  apply (DY.morphisms _ _).injective
  apply DeformationMorphism.ext_of_components
  · have e₁ := DY.morphism_projection (G.toFunctor.map f)
    have e₂ := DY.morphism_projection
      (eqToHom (hobj c) ≫ G'.toFunctor.map f ≫ eqToHom (hobj d).symm)
    have p₁ := Functor.congr_hom G.projection_comm f
    have p₂ := Functor.congr_hom G'.projection_comm f
    simp only [Functor.comp_map] at p₁ p₂
    rw [← e₁, ← e₂, p₁, Functor.map_comp, Functor.map_comp, p₂, eqToHom_map, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  · rw [predeformation_morphisms_conj_arrow, G.morphism_arrow f, G'.morphism_arrow f]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end Uniqueness

section SelfIntersection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
variable (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (Φ : 𝒳 ⥤ 𝒴)
  (hΦ : Φ ⋙ p𝒴 = p𝒳) (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
  (hx₀ : (p𝒳 ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The diagonal object `(x₀, x₀, id)` of the self-intersection `𝒳 ×_{Φ, 𝒴, Φ} 𝒳`. -/
def selfIntersectionPoint : TwoFibreProductOver p𝒳 p𝒳 p𝒴 Φ Φ :=
  ⟨p𝒳.obj x₀, x₀, x₀, rfl, rfl, Iso.refl _, by
    have hbase : p𝒴.obj (Φ.obj x₀) = p𝒳.obj x₀ := Functor.congr_obj hΦ x₀
    change p𝒴.IsHomLift (𝟙 (p𝒳.obj x₀)) (𝟙 (Φ.obj x₀))
    rw [← hbase]
    infer_instance⟩

include hx₀ in
/-- The diagonal object `(x₀, x₀, id)` of the self-intersection `𝒳 ×_{Φ, 𝒴, Φ} 𝒳` lies over
the composite `Spec k ⟶ Spec Λ ⟶ S`. -/
theorem selfIntersectionPoint_base :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion).obj
      (selfIntersectionPoint B S hS p𝒳 p𝒴 Φ hΦ x₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := hx₀

attribute [local implicit_reducible] TwoFibreProductOver.lift
  TwoFibreProductOver.structureFunctor TwoFibreProductOver.fst TwoFibreProductOver.snd

/-- **Stacks 07WL at the diagonal object of a self-intersection.** The predeformation category
of `𝒲 = 𝒳 ×_{Φ, 𝒴, Φ} 𝒳` at `(x₀, x₀, id)` is equivalent over `𝒞_Λ` to the 2-fibre product of
`𝓕_{𝒳,k,x₀}` with itself over `𝓕_{𝒴,k,Φ(x₀)}` along the functor induced by `Φ`. -/
noncomputable def selfIntersectionPredeformationEquivalence
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hRS𝒳 : SatisfiesRS B S hS p𝒳 h𝒳) (hRS𝒴 : SatisfiesRS B S hS p𝒴 h𝒴)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let w₀ := selfIntersectionPoint B S hS p𝒳 p𝒴 Φ hΦ x₀
    let hF : Φ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒳 ⋙ Over.post B.inclusion :=
      congrArg (fun H => H ⋙ Over.post B.inclusion) hΦ
    let D𝒲 := predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion) w₀
      (selfIntersectionPoint_base B S hS p𝒳 p𝒴 Φ hΦ iΛ x₀ hx₀)
    let D𝒳 := predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion) x₀ hx₀
    let mF := mapPredeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) Φ hF x₀ hx₀
    letI := D𝒲.category
    letI := D𝒳.category
    letI := (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion) (Φ.obj x₀)
      (imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ (p𝒳 ⋙ Over.post B.inclusion) Φ hF
        x₀ hx₀)).category
    StacksRepresentableCFG.EquivalenceOver D𝒲.projection
      (TwoFibreProductOver.structureFunctor D𝒳.projection D𝒳.projection
        (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion) (Φ.obj x₀)
          (imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ (p𝒳 ⋙ Over.post B.inclusion) Φ
            hF x₀ hx₀)).projection
        mF.toFunctor mF.toFunctor) := by
  intro w₀ hF D𝒲 D𝒳 mF
  letI : Category (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.snd p𝒳 p𝒳 p𝒴 Φ Φ).obj w₀)
      (imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion)
        (TwoFibreProductOver.snd p𝒳 p𝒳 p𝒴 Φ Φ) (snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒳 Φ Φ) w₀
        (selfIntersectionPoint_base B S hS p𝒳 p𝒴 Φ hΦ iΛ x₀ hx₀))).carrier := D𝒳.category
  letI : Category (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ).obj w₀)
      (imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion)
        (TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ) (fst_comp_post_eq B S hS p𝒳 p𝒴 p𝒳 Φ Φ) w₀
        (selfIntersectionPoint_base B S hS p𝒳 p𝒴 Φ hΦ iΛ x₀ hx₀))).carrier := D𝒳.category
  let hw₀base := selfIntersectionPoint_base B S hS p𝒳 p𝒴 Φ hΦ iΛ x₀ hx₀
  let hA := fst_comp_post_eq B S hS p𝒳 p𝒴 p𝒳 Φ Φ
  let hB := snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒳 Φ Φ
  let data := fibreProductOfPredeformationCategoriesOfEssSurj iΛ
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion)
    (p𝒳 ⋙ Over.post B.inclusion) (p𝒳 ⋙ Over.post B.inclusion)
    (p𝒴 ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ)
    (TwoFibreProductOver.snd p𝒳 p𝒳 p𝒴 Φ Φ) Φ Φ hA hB hF
    (TwoFibreProductOver.psiIso p𝒳 p𝒳 p𝒴 Φ Φ) w₀ hw₀base hF
    (isHomLift_psiIso_post B S hS p𝒳 p𝒴 p𝒳 Φ Φ)
    (exists_liftPost_iso_over_base B S hS p𝒳 p𝒴 p𝒳 Φ Φ)
    (isEquivalence_liftPost B S hS p𝒳 p𝒴 p𝒳 Φ Φ)
  let D𝒴 := predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion) (Φ.obj x₀)
    (imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ (p𝒳 ⋙ Over.post B.inclusion) Φ hF x₀ hx₀)
  letI := D𝒳.category
  letI := D𝒲.category
  letI := D𝒴.category
  letI : Category (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
      (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ).obj w₀))
      (imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ (p𝒳 ⋙ Over.post B.inclusion) Φ hF
        ((TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ).obj w₀)
        (imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ ⋙ Over.post B.inclusion)
          (TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ) hA w₀ hw₀base))).carrier := D𝒴.category
  -- the transported right leg is the induced functor, `ψ(w₀)` being the identity
  have hpsi : (TwoFibreProductOver.psiIso p𝒳 p𝒳 p𝒴 Φ Φ).hom.app w₀ = 𝟙 _ := rfl
  -- the fields of the right leg, read in the forms of the statement
  let R : D𝒳.carrier ⥤ D𝒴.carrier := data.rightFunctor
  have Rproj : R ⋙ D𝒴.projection = D𝒳.projection := data.rightFunctor_projection
  have Rpoint : ∀ c, (D𝒴.objects (R.obj c)).point = Φ.obj (D𝒳.objects c).point :=
    data.rightFunctor_point
  have Rarrow : ∀ c, (D𝒴.objects (R.obj c)).arrow =
      Φ.map (D𝒳.objects c).arrow ≫ eqToHom (Rpoint c).symm := by
    intro c
    have h := data.rightFunctor_arrow c
    rw [hpsi] at h
    exact h.trans (Category.id_comp _)
  let G : InducedPredeformationFunctor iΛ (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) Φ hF x₀ hx₀ :=
    ⟨R, Rproj, Rpoint, Rarrow, fun f => data.rightFunctor_map_arrow f⟩
  have hR : R = mF.toFunctor := G.toFunctor_eq mF
  have hcofW : IsCofiberedInGroupoids D𝒲.projection :=
    (isDeformationCategory_predeformationCategory B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒴 Φ Φ)
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒳 p𝒴 Φ Φ h𝒳 h𝒳 h𝒴 hΦ hΦ)
      (satisfiesRS_twoFibreProductOver B S hS p𝒳 p𝒴 p𝒳 Φ Φ h𝒳 h𝒴 h𝒳 hΦ hΦ
        hRS𝒳 hRS𝒴 hRS𝒳) iΛ w₀ hw₀base hfinite hqc).predeformation.cofibered
  letI : Category (TwoFibreProductOver D𝒳.projection D𝒳.projection D𝒴.projection mF.toFunctor
      data.rightFunctor) := TwoFibreProductOver.instCategory
  let mA := mapPredeformationCategory iΛ _ _ (TwoFibreProductOver.fst p𝒳 p𝒳 p𝒴 Φ Φ) hA w₀ hw₀base
  let mB := mapPredeformationCategory iΛ _ _ (TwoFibreProductOver.snd p𝒳 p𝒳 p𝒴 Φ Φ) hB w₀ hw₀base
  let L := TwoFibreProductOver.lift D𝒳.projection D𝒳.projection D𝒴.projection mF.toFunctor
    data.rightFunctor D𝒲.projection mA.toFunctor mB.toFunctor mA.projection_comm
    mB.projection_comm data.filler data.filler_vertical
  haveI : L.IsEquivalence := data.isEquivalence
  let E₁ := equivalenceOverOfCofibered hcofW L
    (TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _)
  refine E₁.trans (twoFibreProductEquivalenceOverOfIso mF.toFunctor (eqToIso hR) ?_)
  intro y
  have hy : (eqToIso hR).hom.app y = eqToHom (Functor.congr_obj hR y) := eqToHom_app hR y
  rw [hy]
  exact IsHomLift.eqToHom_domain_lift_id _ (Functor.congr_obj Rproj y)

end SelfIntersection

end Deformation.Artin

end
