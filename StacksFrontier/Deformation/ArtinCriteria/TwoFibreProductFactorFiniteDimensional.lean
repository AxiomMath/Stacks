module

public import StacksFrontier.Deformation.ArtinCriteria.TwoFibreProductFiniteDimensional
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensionalEndpoints
public import StacksFrontier.Deformation.Artin.TangentSpaceVectorStructure

/-!
# Finite-dimensional tangent spaces of a factor of a 2-fibre product

Let `Φ : 𝒳 ⟶ 𝒴` and `Ψ : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the big
fppf site of `S` satisfying (RS), and let `w₀` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over a field `k` of
finite type over `S`.  Exactness of the sequence of Stacks 07X2,

`0 → Inf(𝓕_𝒲) → Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵) → Inf(𝓕_𝒴) → T𝓕_𝒲 → T𝓕_𝒳 ⊕ T𝓕_𝒵 → T𝓕_𝒴`,

at its two direct sums bounds the factor `𝒳` by `𝒲` and `𝒴`.  This is the direction used in the
proof of Stacks 0DLL ("by Lemma 07X2 we reduce to proving that `B`, `Spec(k)` and `𝒳₀` have finite
dimensional tangent spaces and infinitesimal automorphism spaces"), where `𝒲 = 𝒳₀` is the fibre of
`𝒳 = Complexes_{X/B}` over `Spec k ⟶ B`:

* `Deformation.Artin.finiteDimensional_tangentModuleAt_fst_twoFibreProduct`: if `T𝓕_𝒲` and
  `T𝓕_𝒴` are finite dimensional, so is `T𝓕_𝒳`, by exactness at `T𝓕_𝒳 ⊕ T𝓕_𝒵`;
* `Deformation.Artin.finiteDimensional_inf_fst_twoFibreProduct`: if `Inf(𝓕_𝒲)` and `Inf(𝓕_𝒴)`
  are finite dimensional, so is `Inf(𝓕_𝒳)`, at every point of the special fibre and for every
  choice of pushforwards, by exactness at `Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵)`;
* `Deformation.Artin.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct`: the
  two together, for the vector spaces of Stacks 07WY.

Tangent spaces are read in `Deformation.tangentModuleAt` at the rank-one module `k`, and
infinitesimal automorphisms in `Deformation.localizedAutomorphismFunctorTangent`, as in
`StacksFrontier/Deformation/ArtinCriteria/TwoFibreProductFiniteDimensional.lean`.

## References

* [Stacks Project, Tag 07X2](https://stacks.math.columbia.edu/tag/07X2)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
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

/-- The shared core of the two finite-dimensionality statements for the first factor of a
2-fibre product: the tangent spaces (resp. infinitesimal automorphisms) of `𝒳` are finite
dimensional when those of `𝒲` and `𝒴` are, by exactness of the sequence of Stacks 07X2. -/
private theorem finiteDimensional_fst_twoFibreProduct_aux
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
  let hF : Φ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒳 ⋙ Over.post B.inclusion :=
    congrArg (fun H => H ⋙ Over.post B.inclusion) hΦ
  let hX := imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) hA w₀ hw₀base
  let hY := imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ
    (p𝒳 ⋙ Over.post B.inclusion) Φ hF ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
  let D𝒲 := predeformationCategory iΛ
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀ hw₀base
  let D𝒳 := predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
    ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
  let D𝒴 := predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
    (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hY
  letI := D𝒲.category
  letI := D𝒳.category
  letI := D𝒴.category
  ((∀ hD : IsDeformationCategory.{u, u, u} D𝒲.projection,
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor D𝒲.projection) hD (FGModuleCat.of k k))) →
  (∀ hD : IsDeformationCategory.{u, u, u} D𝒴.projection,
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor D𝒴.projection) hD (FGModuleCat.of k k))) →
  ∀ hD : IsDeformationCategory.{u, u, u} D𝒳.projection,
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor D𝒳.projection) hD (FGModuleCat.of k k))) ∧
  ((∀ (hD : IsDeformationCategory.{u, u, u} D𝒲.projection) (x : D𝒲.carrier)
    (_hx : D𝒲.projection.obj x = residueFieldObject Λ k)
    (P : ChosenPushforwardsAt D𝒲.projection x),
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P)) →
  (∀ (hD : IsDeformationCategory.{u, u, u} D𝒴.projection) (x : D𝒴.carrier)
    (_hx : D𝒴.projection.obj x = residueFieldObject Λ k)
    (P : ChosenPushforwardsAt D𝒴.projection x),
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P)) →
  ∀ (hD : IsDeformationCategory.{u, u, u} D𝒳.projection) (x : D𝒳.carrier)
    (_hx : D𝒳.projection.obj x = residueFieldObject Λ k)
    (P : ChosenPushforwardsAt D𝒳.projection x),
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P)) := by
  intro hA hF hX hY D𝒲 D𝒳 D𝒴
  let hB := snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
  let hG : Ψ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒵 ⋙ Over.post B.inclusion :=
    congrArg (fun H => H ⋙ Over.post B.inclusion) hΨ
  let hZ := imageBasePoint (qY := p𝒵 ⋙ Over.post B.inclusion) iΛ
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
    (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) hB w₀ hw₀base
  let D𝒵 := predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
    ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hZ
  let := D𝒵.category
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
  let hw₀ : (mF.toFunctor ⋙ D𝒴.projection).obj (mA.toFunctor.obj w₀'.1) =
      Deformation.residueFieldObject Λ k :=
    (Functor.congr_obj mF.projection_comm (mA.toFunctor.obj w₀'.1)).trans
      ((Functor.congr_obj mA.projection_comm w₀'.1).trans w₀'.2)
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
  refine ⟨fun hT𝒲 hT𝒴 hD => ?_, fun hInf𝒲 hInf𝒴 hD x hxk P => ?_⟩
  · have h5 := (sixTermExact_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
      hRS𝒵 w₀ hw₀base hfinite hqc).2.2.2.2
    have hTW : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor D𝒲.projection) hD𝒲 (FGModuleCat.of k (ULift.{u} k))) :=
      (finiteDimensional_tangentModuleAt_uLift_iff hD𝒲).mpr (hT𝒲 hD𝒲)
    have hTY : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor D𝒴.projection) hD𝒴 (FGModuleCat.of k (ULift.{u} k))) :=
      (finiteDimensional_tangentModuleAt_uLift_iff hD𝒴).mpr (hT𝒴 hD𝒴)
    have hsum : FiniteDimensional k (↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection)) hH'
        (FGModuleCat.of k (ULift.{u} k))) × ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection)) hG'
        (FGModuleCat.of k (ULift.{u} k)))) :=
      Deformation.Examples.finiteDimensional_of_exact h5
    have hTH : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection)) hH'
        (FGModuleCat.of k (ULift.{u} k))) :=
      Module.Finite.of_surjective (LinearMap.fst k _ ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection)) hG'
        (FGModuleCat.of k (ULift.{u} k)))) LinearMap.fst_surjective
    rwa [finiteDimensional_tangentModuleAt_uLift_iff hH',
      finiteDimensional_tangentModuleAt_congr mF.projection_comm hH' hD𝒳] at hTH
  · have h2 := (sixTermExact_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
      hRS𝒵 w₀ hw₀base hfinite hqc).2.1
    have hxA : D𝒳.projection.obj (mA.toFunctor.obj w₀'.1) = residueFieldObject Λ k :=
      (Functor.congr_obj mA.projection_comm w₀'.1).trans w₀'.2
    have hPW : FiniteDimensional k (localizedAutomorphismFunctorTangent PW) :=
      hInf𝒲 hD𝒲 w₀'.1 w₀'.2 PW
    have hPF : FiniteDimensional k (localizedAutomorphismFunctorTangent PF) :=
      hInf𝒴 hD𝒴 _ hw₀ PF
    have hsum : FiniteDimensional k (localizedAutomorphismFunctorTangent QH ×
        localizedAutomorphismFunctorTangent QG) :=
      Deformation.Examples.finiteDimensional_of_exact h2
    have hQH : FiniteDimensional k (localizedAutomorphismFunctorTangent QH) :=
      Module.Finite.of_surjective (LinearMap.fst k _ (localizedAutomorphismFunctorTangent QG))
        LinearMap.fst_surjective
    let PX := chosenPushforwardsAtOfCofiberedInGroupoids hD𝒳.predeformation.cofibered
      (mA.toFunctor.obj w₀'.1)
    obtain ⟨j, -⟩ := existsUnique_pointIso hD𝒳.predeformation ⟨x, hxk⟩
      ⟨mA.toFunctor.obj w₀'.1, hxA⟩
    exact finiteDimensional_localizedAutomorphismFunctorTangent_of_hom hD.satisfiesRS j.hom.1
      hxA P PX (finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful (𝟭 _)
        ((Functor.id_comp _).trans mF.projection_comm) hD𝒳.satisfiesRS hH'.satisfiesRS PX QH hQH)

/-- **Finite-dimensional tangent spaces for the first factor of a 2-fibre product** (exactness
at `T𝓕_𝒳 ⊕ T𝓕_𝒵` in Stacks 07X2): the tangent space of `𝒳` at the first projection of `w₀` is
finite dimensional as soon as those of `𝒲 = 𝒳 ×_𝒴 𝒵` at `w₀` and of `𝒴` at the image of `w₀`
are.  The kernel of `T𝓕_𝒳 ⊕ T𝓕_𝒵 → T𝓕_𝒴` is the image of `T𝓕_𝒲`. -/
theorem finiteDimensional_tangentModuleAt_fst_twoFibreProduct
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
    (hT𝒲 : ∀ hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection,
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
          hw₀base).projection) hD (FGModuleCat.of k k)))
    (hT𝒴 : ∀ (hy : (p𝒴 ⋙ Over.post B.inclusion).obj
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
          (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection) hD
        (FGModuleCat.of k k)))
    (hx : (p𝒳 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒳 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hx).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection) hD
      (FGModuleCat.of k k)) := by
  exact (finiteDimensional_fst_twoFibreProduct_aux B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
        hRS𝒵 w₀ hw₀base hfinite hqc).1 hT𝒲 (hT𝒴 _) hD

/-- **Finite-dimensional infinitesimal automorphisms for the first factor of a 2-fibre product**
(exactness at `Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵)` in Stacks 07X2): the infinitesimal automorphisms of `𝒳` at
the first projection of `w₀` are finite dimensional, at every point of the special fibre and for
every choice of pushforwards, as soon as those of `𝒲 = 𝒳 ×_𝒴 𝒵` at `w₀` and of `𝒴` at the image
of `w₀` are.  The kernel of `Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵) → Inf(𝓕_𝒴)` is the image of `Inf(𝓕_𝒲)`. -/
theorem finiteDimensional_inf_fst_twoFibreProduct
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
    (hInf𝒲 : ∀ (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection)
      (x : (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).carrier)
      (_hx : (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection.obj x = residueFieldObject Λ k)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection x),
      letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
      letI := naturalLocalizedTangentModule P hD.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
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
    (hx : (p𝒳 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒳 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)
        hx).projection)
    (x : (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).carrier)
    (hxk : (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection.obj x =
        residueFieldObject Λ k)
    (P : ChosenPushforwardsAt (predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx).projection x) :
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  exact (finiteDimensional_fst_twoFibreProduct_aux B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴
        hRS𝒵 w₀ hw₀base hfinite hqc).2 hInf𝒲 (hInf𝒴 _) hD x hxk P

/-- **The vector spaces of Stacks 07WY for the first factor of a 2-fibre product.**  The tangent
space `T𝓕_{𝒳,k,x₀}` and the infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` of `𝒳` at the first
projection `x₀` of `w₀`, with their vector-space structures of Stacks 07WY
(`Deformation.Artin.tangentSpaceModuleOfSatisfiesRS` and
`Deformation.Artin.infinitesimalAutomorphismModuleOfSatisfiesRS`), are finite dimensional as soon
as those of `𝒲 = 𝒳 ×_𝒴 𝒵` at `w₀` and of `𝒴` at the image of `w₀` are: Stacks 07X2, exactness
at the two direct sums, through
`Deformation.Artin.finiteDimensional_tangentModuleAt_fst_twoFibreProduct` and
`Deformation.Artin.finiteDimensional_inf_fst_twoFibreProduct`. -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct
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
    (hT𝒲 : ∀ hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection,
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
          hw₀base).projection) hD (FGModuleCat.of k k)))
    (hT𝒴 : ∀ (hy : (p𝒴 ⋙ Over.post B.inclusion).obj
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒴 ⋙ Over.post B.inclusion)
        (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
          (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hy).projection) hD
        (FGModuleCat.of k k)))
    (hInf𝒲 : ∀ (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection)
      (x : (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).carrier)
      (_hx : (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection.obj x = residueFieldObject Λ k)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀
        hw₀base).projection x),
      letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
      letI := naturalLocalizedTangentModule P hD.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
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
    (hx : (p𝒳 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS p𝒳 h𝒳 hRS𝒳 iΛ
        ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS p𝒳 h𝒳
        hRS𝒳 iΛ ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx hfinite hqc x P) := by
  let hD := isDeformationCategory_predeformationCategory B S hS p𝒳 h𝒳 hRS𝒳 iΛ
    ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hx hfinite hqc
  refine ⟨?_, fun x P => ?_⟩
  · exact finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt hD
      ((finiteDimensional_tangentModuleAt_uLift_iff hD).mpr
        (finiteDimensional_tangentModuleAt_fst_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ w₀
          hw₀base hΦ hΨ h𝒳 h𝒴 h𝒵 hRS𝒳 hRS𝒴 hRS𝒵 hfinite hqc hT𝒲 hT𝒴 hx hD))
  · exact finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hD.satisfiesRS P
      (finiteDimensional_inf_fst_twoFibreProduct B S hS iΛ p𝒳 p𝒴 p𝒵 Φ Ψ hΦ hΨ h𝒳 h𝒴 h𝒵
        hRS𝒳 hRS𝒴 hRS𝒵 w₀ hw₀base hfinite hqc hInf𝒲 hInf𝒴 hx hD x.1 x.2 P)

end Deformation.Artin
