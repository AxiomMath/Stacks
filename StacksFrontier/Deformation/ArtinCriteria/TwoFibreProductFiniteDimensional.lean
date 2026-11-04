module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransport
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace

/-!
# Finite-dimensional tangent spaces and infinitesimal automorphisms of a 2-fibre product

Let `Φ : 𝒳 ⟶ 𝒴` and `Ψ : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the big
fppf site of `S` satisfying (RS), and let `w₀` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over a field `k` of
finite type over `S`. The exact sequence of Stacks 07X2,

`0 → Inf(𝓕_𝒲) → Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵) → Inf(𝓕_𝒴) → T𝓕_𝒲 → T𝓕_𝒳 ⊕ T𝓕_𝒵 → T𝓕_𝒴`,

gives the two finiteness statements used in the proof of Stacks 07Y5 ("Axiom [3] for `Y` follows
from Lemmas 07X1 and 07X2"):

* `Deformation.Artin.finiteDimensional_tangentModuleAt_twoFibreProduct`: if `T𝓕_𝒳`, `T𝓕_𝒵`
  and `Inf(𝓕_𝒴)` are finite dimensional, so is `T𝓕_𝒲`, by exactness at `T𝓕_𝒲`;
* `Deformation.Artin.finiteDimensional_inf_twoFibreProduct`: if `Inf(𝓕_𝒳)` and `Inf(𝓕_𝒵)` are
  finite dimensional, so is `Inf(𝓕_𝒲)`, at every point of the special fibre and for every choice
  of pushforwards, by injectivity of the first map.

Tangent spaces are read in `Deformation.tangentModuleAt` at the rank-one module `k`, and
infinitesimal automorphisms in `Deformation.localizedAutomorphismFunctorTangent` with its natural
vector-space structure, the two forms in which Stacks 07X2 is stated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace Deformation.Artin

universe u u₁ v₁ u₂ v₂ u₃ v₃

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (iΛ : Spec (.of Λ) ⟶ S)
variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
variable (p𝒳 : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (p𝒵 : 𝒵 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (Φ : 𝒳 ⥤ 𝒴) (Ψ : 𝒵 ⥤ 𝒴)

/-- Every infinitesimal automorphism space of `p` at a point of the special fibre, for every choice
of pushforwards, is finite dimensional. -/
private def AllInfFiniteDimensional {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    (p : 𝒞 ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k) : Prop :=
  ∀ (hD : IsDeformationCategory.{u, u, u} p) (x : 𝒞) (_ : p.obj x = residueFieldObject Λ k)
    (P : ChosenPushforwardsAt p x),
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P)

/-- The common setup for the 2-fibre product: the finiteness statements for the tangent space and
the infinitesimal automorphisms of `𝒲`, in terms of the predeformation categories of `𝒲`, `𝒳`,
`𝒴`, `𝒵`. -/
private theorem finiteDimensional_twoFibreProduct_aux
    (hΦ : Φ ⋙ p𝒴 = p𝒳) (hΨ : Ψ ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hRS𝒳 : SatisfiesRS B S hS p𝒳 h𝒳) (hRS𝒴 : SatisfiesRS B S hS p𝒴 h𝒴)
    (hRS𝒵 : SatisfiesRS B S hS p𝒵 h𝒵)
    (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ)
    (hw₀base : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
      Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let hA := fst_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
    let hB := snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
    let hF : Φ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒳 ⋙ Over.post B.inclusion :=
      congrArg (fun H => H ⋙ Over.post B.inclusion) hΦ
    let hG : Ψ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒵 ⋙ Over.post B.inclusion :=
      congrArg (fun H => H ⋙ Over.post B.inclusion) hΨ
    let hX := imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) hA w₀ hw₀base
    let hZ := imageBasePoint (qY := p𝒵 ⋙ Over.post B.inclusion) iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) hB w₀ hw₀base
    let hY := imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ
      (p𝒳 ⋙ Over.post B.inclusion) Φ hF ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let D𝒲 := predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀ hw₀base
    let D𝒳 := predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let D𝒵 := predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hZ
    let D𝒴 := predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
      (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hY
    let := D𝒲.category
    let := D𝒳.category
    let := D𝒵.category
    let := D𝒴.category
    let mA := mapPredeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒳 ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) hA w₀ hw₀base
    let mB := mapPredeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒵 ⋙ Over.post B.inclusion) (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) hB w₀ hw₀base
    let mF := mapPredeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) Φ hF
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let data := fibreProductOfPredeformationCategoriesOfEssSurj iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒳 ⋙ Over.post B.inclusion) (p𝒵 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ)
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) Φ Ψ hA hB hF
      (TwoFibreProductOver.psiIso p𝒳 p𝒵 p𝒴 Φ Ψ) w₀ hw₀base hG
      (isHomLift_psiIso_post B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
      (exists_liftPost_iso_over_base B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
      (isEquivalence_liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
    let hD𝒲 := isDeformationCategory_predeformationCategory B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ)
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 Φ Ψ h𝒳 h𝒵 h𝒴 hΦ hΨ)
      (satisfiesRS_twoFibreProductOver B S hS p𝒳 p𝒴 p𝒵 Φ Ψ h𝒳 h𝒴 h𝒵 hΦ hΨ
        hRS𝒳 hRS𝒴 hRS𝒵) iΛ w₀ hw₀base hfinite hqc
    let hD𝒳 := isDeformationCategory_predeformationCategory B S hS p𝒳 h𝒳 hRS𝒳 iΛ
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX hfinite hqc
    let hD𝒵 := isDeformationCategory_predeformationCategory B S hS p𝒵 h𝒵 hRS𝒵 iΛ
      ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hZ hfinite hqc
    let hD𝒴 := isDeformationCategory_predeformationCategory B S hS p𝒴 h𝒴 hRS𝒴 iΛ
      (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hY hfinite hqc
    let hA' : mA.toFunctor ⋙ (mF.toFunctor ⋙ D𝒴.projection) = D𝒲.projection :=
      (congrArg (mA.toFunctor ⋙ ·) mF.projection_comm).trans mA.projection_comm
    let hB' : mB.toFunctor ⋙ (data.rightFunctor ⋙ D𝒴.projection) = D𝒲.projection :=
      (congrArg (mB.toFunctor ⋙ ·) data.rightFunctor_projection).trans mB.projection_comm
    let hH' : IsDeformationCategory (mF.toFunctor ⋙ D𝒴.projection) := mF.projection_comm ▸ hD𝒳
    let hG' : IsDeformationCategory (data.rightFunctor ⋙ D𝒴.projection) :=
      data.rightFunctor_projection ▸ hD𝒵
    let hlift' : (TwoFibreProductOver.lift (mF.toFunctor ⋙ D𝒴.projection)
        (data.rightFunctor ⋙ D𝒴.projection) D𝒴.projection mF.toFunctor data.rightFunctor
        D𝒲.projection mA.toFunctor mB.toFunctor hA' hB' data.filler
        data.filler_vertical).IsEquivalence :=
      Deformation.isEquivalence_lift_congr D𝒴.projection D𝒲.projection mF.toFunctor
        data.rightFunctor mA.toFunctor mB.toFunctor D𝒳.projection
        (mF.toFunctor ⋙ D𝒴.projection) mF.projection_comm.symm D𝒵.projection
        (data.rightFunctor ⋙ D𝒴.projection) data.rightFunctor_projection.symm
        mA.projection_comm hA' mB.projection_comm hB' data.filler data.filler_vertical
        data.isEquivalence
    let := hlift'
    let w₀' : D𝒲.projection.Fiber (Deformation.residueFieldObject Λ k) :=
      (Classical.choice hD𝒲.predeformation.specialFiber).inverse.obj ⟨PUnit.unit⟩
    let PW := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids
      hD𝒲.predeformation.cofibered w₀'.1
    let QH := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids
      hH'.predeformation.cofibered (mA.toFunctor.obj w₀'.1)
    let QG := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids
      hG'.predeformation.cofibered (mB.toFunctor.obj w₀'.1)
    let PF := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids
      hD𝒴.predeformation.cofibered (mF.toFunctor.obj (mA.toFunctor.obj w₀'.1))
    let := Deformation.naturalLocalizedTangentAddCommGroup PW hD𝒲.satisfiesRS
    let := Deformation.naturalLocalizedTangentModule PW hD𝒲.satisfiesRS
    let := Deformation.naturalLocalizedTangentAddCommGroup QH hH'.satisfiesRS
    let := Deformation.naturalLocalizedTangentModule QH hH'.satisfiesRS
    let := Deformation.naturalLocalizedTangentAddCommGroup QG hG'.satisfiesRS
    let := Deformation.naturalLocalizedTangentModule QG hG'.satisfiesRS
    let := Deformation.naturalLocalizedTangentAddCommGroup PF hD𝒴.satisfiesRS
    let := Deformation.naturalLocalizedTangentModule PF hD𝒴.satisfiesRS
  (FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor D𝒳.projection) hD𝒳
        (FGModuleCat.of k k)) →
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor D𝒵.projection) hD𝒵
        (FGModuleCat.of k k)) →
      AllInfFiniteDimensional D𝒴.projection →
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor D𝒲.projection) hD𝒲
        (FGModuleCat.of k k))) ∧
    (AllInfFiniteDimensional D𝒳.projection → AllInfFiniteDimensional D𝒵.projection →
      AllInfFiniteDimensional D𝒲.projection) := by
  intro hA hB hF hG hX hZ hY D𝒲 D𝒳 D𝒵 D𝒴 _ _ _ _ mA mB mF data hD𝒲 hD𝒳 hD𝒵 hD𝒴 hA' hB' hH' hG'
    hlift' _ w₀' PW QH QG PF _ _ _ _ _ _ _ _
  have hxA : D𝒳.projection.obj (mA.toFunctor.obj w₀'.1) = residueFieldObject Λ k :=
    (Functor.congr_obj mA.projection_comm w₀'.1).trans w₀'.2
  have hxB : D𝒵.projection.obj (mB.toFunctor.obj w₀'.1) = residueFieldObject Λ k :=
    (Functor.congr_obj mB.projection_comm w₀'.1).trans w₀'.2
  refine ⟨fun hTX hTZ hInfY => ?_, fun hInfX hInfZ hD x hx P => ?_⟩
  · have h4 := (sixTermExact_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
      hRS𝒵 w₀ hw₀base hfinite hqc).2.2.2.1
    have hInf := hInfY hD𝒴 _ ((Functor.congr_obj mF.projection_comm _).trans hxA) PF
    have hTH : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection)) hH'
        (FGModuleCat.of k (ULift.{u} k))) := by
      rw [finiteDimensional_tangentModuleAt_uLift_iff hH',
        finiteDimensional_tangentModuleAt_congr mF.projection_comm hH' hD𝒳]
      exact hTX
    have hTG : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection)) hG'
        (FGModuleCat.of k (ULift.{u} k))) := by
      rw [finiteDimensional_tangentModuleAt_uLift_iff hG',
        finiteDimensional_tangentModuleAt_congr data.rightFunctor_projection hG' hD𝒵]
      exact hTZ
    have hW := Module.finiteDimensional_of_exact _ _ h4
    exact (finiteDimensional_tangentModuleAt_uLift_iff hD𝒲).mp hW
  · have h1 := (sixTermExact_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
      hRS𝒵 w₀ hw₀base hfinite hqc).1
    have hQH : FiniteDimensional k (localizedAutomorphismFunctorTangent QH) :=
      finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful (𝟭 _)
        ((Functor.id_comp _).trans mF.projection_comm.symm) hH'.satisfiesRS hD𝒳.satisfiesRS QH
        (chosenPushforwardsAtOfCofiberedInGroupoids hD𝒳.predeformation.cofibered
          (mA.toFunctor.obj w₀'.1))
        (hInfX hD𝒳 _ hxA _)
    have hQG : FiniteDimensional k (localizedAutomorphismFunctorTangent QG) :=
      finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful (𝟭 _)
        ((Functor.id_comp _).trans data.rightFunctor_projection.symm) hG'.satisfiesRS
        hD𝒵.satisfiesRS QG
        (chosenPushforwardsAtOfCofiberedInGroupoids hD𝒵.predeformation.cofibered
          (mB.toFunctor.obj w₀'.1))
        (hInfZ hD𝒵 _ hxB _)
    have hPW : FiniteDimensional k (localizedAutomorphismFunctorTangent PW) :=
      Module.Finite.of_injective _ h1
    obtain ⟨j, -⟩ := existsUnique_pointIso hD𝒲.predeformation ⟨x, hx⟩ w₀'
    exact finiteDimensional_localizedAutomorphismFunctorTangent_of_hom hD.satisfiesRS j.hom.1
      w₀'.2 P PW hPW

/-- **Finite-dimensional tangent spaces for a 2-fibre product** (exactness at `T𝓕_𝒲` in
Stacks 07X2): the tangent space of `𝒲 = 𝒳 ×_𝒴 𝒵` at `w₀` is finite dimensional as soon as those
of `𝒳` and `𝒵` at the projections of `w₀` and the infinitesimal automorphisms of `𝒴` at the
image of `w₀` are. -/
theorem finiteDimensional_tangentModuleAt_twoFibreProduct
    (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ)
    (hw₀base : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
      Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hΦ : Φ ⋙ p𝒴 = p𝒳) (hΨ : Ψ ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hRS𝒳 : SatisfiesRS B S hS p𝒳 h𝒳) (hRS𝒴 : SatisfiesRS B S hS p𝒴 h𝒴)
    (hRS𝒵 : SatisfiesRS B S hS p𝒵 h𝒵)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒳 : ∀ (hx : (p𝒳 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒳 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hx).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
          ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection) hD
        (FGModuleCat.of k k)))
    (hT𝒵 : ∀ (hz : (p𝒵 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hz).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
          ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hz).projection) hD
        (FGModuleCat.of k k)))
    (hInf𝒴 : ∀ (hy : (p𝒴 ⋙ Over.post B.inclusion).obj
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection)
      (x : (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).carrier)
      (_hx : (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection.obj x =
        residueFieldObject Λ k)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection x),
      letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
      letI := naturalLocalizedTangentModule P hD.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
      hw₀base).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection) hD (FGModuleCat.of k k)) := by
  exact (finiteDimensional_twoFibreProduct_aux B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳
    hRS𝒴 hRS𝒵 w₀ hw₀base hfinite hqc).1 (hT𝒳 _ _) (hT𝒵 _ _) (hInf𝒴 _)

/-- **Finite-dimensional infinitesimal automorphisms for a 2-fibre product** (injectivity of
`Inf(𝓕_𝒲) → Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵)` in Stacks 07X2): the infinitesimal automorphisms of
`𝒲 = 𝒳 ×_𝒴 𝒵` at `w₀` are finite dimensional, at every point of the special fibre and for every
choice of pushforwards, as soon as those of `𝒳` and `𝒵` at the projections of `w₀` are. -/
theorem finiteDimensional_inf_twoFibreProduct
    (hΦ : Φ ⋙ p𝒴 = p𝒳) (hΨ : Ψ ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hRS𝒳 : SatisfiesRS B S hS p𝒳 h𝒳) (hRS𝒴 : SatisfiesRS B S hS p𝒴 h𝒴)
    (hRS𝒵 : SatisfiesRS B S hS p𝒵 h𝒵)
    (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ)
    (hw₀base : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
      Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hInf𝒳 : ∀ (hx : (p𝒳 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒳 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hx).projection)
      (x : (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).carrier)
      (_hx : (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection.obj x =
        residueFieldObject Λ k)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection x),
      letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
      letI := naturalLocalizedTangentModule P hD.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
    (hInf𝒵 : ∀ (hz : (p𝒵 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hz).projection)
      (x : (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hz).carrier)
      (_hx : (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hz).projection.obj x =
        residueFieldObject Λ k)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hz).projection x),
      letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
      letI := naturalLocalizedTangentModule P hD.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
      hw₀base).projection)
    (x : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
      hw₀base).carrier)
    (hx : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
      hw₀base).projection.obj x = residueFieldObject Λ k)
    (P : ChosenPushforwardsAt (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
      hw₀base).projection x) :
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  exact (finiteDimensional_twoFibreProduct_aux B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳
    hRS𝒴 hRS𝒵 w₀ hw₀base hfinite hqc).2 (hInf𝒳 _) (hInf𝒵 _) hD x hx P

end Deformation.Artin

end
