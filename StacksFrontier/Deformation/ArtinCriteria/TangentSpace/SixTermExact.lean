module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace.SixTermTransfer
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace.SiteComparison

/-!
# The six-term exact sequence for a 2-fibre product of categories fibred in groupoids

The tangent row `T𝓕_𝒲 ⟶ T𝓕_𝒳 ⊕ T𝓕_𝒵 ⟶ T𝓕_𝒴` of a 2-fibre product of categories fibred in
groupoids satisfying (RS) and its exactness
(`Deformation.Artin.exact_tangentRow_twoFibreProduct`), and the full six-term exact sequence of
Stacks 07X2 (`Deformation.Artin.sixTermExact_twoFibreProduct`).
-/

@[expose] public noncomputable section

namespace Deformation.Artin

/-! ### Tangent spaces of a 2-fibre product -/

section TangentSpace
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
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

/-- **Stacks Project, Tag 07X2**, the tangent row.

Let `S` be a locally Noetherian scheme, let `Φ : 𝒳 ⟶ 𝒴` and `Ψ : 𝒵 ⟶ 𝒴` be `1`-morphisms of
categories fibred in groupoids over the big fppf site of `S`, and assume `𝒳`, `𝒴`, `𝒵` satisfy
(RS). Let `k` be a field of finite type over `S` and let `w₀` be an object of
`𝒲 = 𝒳 ×_𝒴 𝒵` over `k`, with induced objects `x₀`, `y₀ = Φ(x₀)`, `z₀` of `𝒳`, `𝒴`, `𝒵`. Then

`T𝓕_{𝒲,k,w₀} ⟶ T𝓕_{𝒳,k,x₀} ⊕ T𝓕_{𝒵,k,z₀} ⟶ T𝓕_{𝒴,k,y₀}`

is an exact sequence of `k`-vector spaces, the first map being the pair of the maps induced by
the two projections of `𝒲` and the second the difference of the maps induced by `Φ` and by `Ψ`
(the latter transported along the comparison isomorphism `ψ(w₀) : Φ(x₀) ≅ Ψ(z₀)`, which is what
makes `y₀ = Φ(x₀)` a legitimate choice of basepoint in `𝒴`).

Because `𝒲` satisfies (RS) (Tag 07WR), all four predeformation categories are deformation
categories (Tag 07WU), so all four tangent spaces carry their canonical `k`-vector space
structures; this is the source's remark that the lemma makes sense. The square of predeformation
categories is a 2-fibre product (Tag 07WL), and the tangent row of a 2-fibre product of
deformation categories is exact at the middle term (part (2) of Tag 06L5), which transports to
the square at hand.

This single conjunct of the full six-term exact sequence is also available, with every clause
proved, as `sixTermExact_twoFibreProduct` below; that theorem carries the `@[stacks 07X2]`
tag. -/
public theorem exact_tangentRow_twoFibreProduct
    (hΦ : Φ ⋙ p𝒴 = p𝒳) (hΨ : Ψ ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hRS𝒳 : SatisfiesRS B S hS p𝒳 h𝒳) (hRS𝒴 : SatisfiesRS B S hS p𝒴 h𝒴)
    (hRS𝒵 : SatisfiesRS B S hS p𝒵 h𝒵)
    (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ)
    (hw₀ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
      Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (M : FGModuleCat.{u} k) :
    let hA := fst_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
    let hB := snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
    let hF : Φ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒳 ⋙ Over.post B.inclusion :=
      congrArg (fun H => H ⋙ Over.post B.inclusion) hΦ
    let hG : Ψ ⋙ p𝒴 ⋙ Over.post B.inclusion = p𝒵 ⋙ Over.post B.inclusion :=
      congrArg (fun H => H ⋙ Over.post B.inclusion) hΨ
    let hX := imageBasePoint (qY := p𝒳 ⋙ Over.post B.inclusion) iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) hA w₀ hw₀
    let hZ := imageBasePoint (qY := p𝒵 ⋙ Over.post B.inclusion) iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) hB w₀ hw₀
    let hY := imageBasePoint (qY := p𝒴 ⋙ Over.post B.inclusion) iΛ
      (p𝒳 ⋙ Over.post B.inclusion) Φ hF ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let D𝒲 := predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion) w₀ hw₀
    let D𝒳 := predeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let D𝒵 := predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hZ
    let D𝒴 := predeformationCategory iΛ (p𝒴 ⋙ Over.post B.inclusion)
      (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hY
    letI := D𝒲.category
    letI := D𝒳.category
    letI := D𝒵.category
    letI := D𝒴.category
    let mA := mapPredeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒳 ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) hA w₀ hw₀
    let mB := mapPredeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒵 ⋙ Over.post B.inclusion) (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) hB w₀ hw₀
    let mF := mapPredeformationCategory iΛ (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) Φ hF
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX
    let data := fibreProductOfPredeformationCategoriesOfEssSurj iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
      (p𝒳 ⋙ Over.post B.inclusion) (p𝒵 ⋙ Over.post B.inclusion)
      (p𝒴 ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ)
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ) Φ Ψ hA hB hF
      (TwoFibreProductOver.psiIso p𝒳 p𝒵 p𝒴 Φ Ψ) w₀ hw₀ hG
      (isHomLift_psiIso_post B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
      (exists_liftPost_iso_over_base B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
      (isEquivalence_liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
    let hD𝒲 := isDeformationCategory_predeformationCategory B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ)
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 Φ Ψ h𝒳 h𝒵 h𝒴 hΦ hΨ)
      (satisfiesRS_twoFibreProductOver B S hS p𝒳 p𝒴 p𝒵 Φ Ψ h𝒳 h𝒴 h𝒵 hΦ hΨ
        hRS𝒳 hRS𝒴 hRS𝒵) iΛ w₀ hw₀ hfinite hqc
    let hD𝒳 := isDeformationCategory_predeformationCategory B S hS p𝒳 h𝒳 hRS𝒳 iΛ
      ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hX hfinite hqc
    let hD𝒵 := isDeformationCategory_predeformationCategory B S hS p𝒵 h𝒵 hRS𝒵 iΛ
      ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀) hZ hfinite hqc
    let hD𝒴 := isDeformationCategory_predeformationCategory B S hS p𝒴 h𝒴 hRS𝒴 iΛ
      (Φ.obj ((TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ).obj w₀)) hY hfinite hqc
    Function.Exact
      (LinearMap.prod
        (Deformation.tangentMapAt.{u, u, u} hD𝒲 hD𝒳
          ({ toFunctor := mA.toFunctor, w := mA.projection_comm } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor D𝒳.projection) M)
        (Deformation.tangentMapAt.{u, u, u} hD𝒲 hD𝒵
          ({ toFunctor := mB.toFunctor, w := mB.projection_comm } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor D𝒵.projection) M))
      ((Deformation.tangentMapAt.{u, u, u} hD𝒳 hD𝒴
            ({ toFunctor := mF.toFunctor, w := mF.projection_comm } :
              BasedCategory.ofFunctor D𝒳.projection ⥤ᵇ
                BasedCategory.ofFunctor D𝒴.projection) M).comp
          (LinearMap.fst k
            ↥(Deformation.tangentModuleAt.{u, u, u}
              (BasedCategory.ofFunctor D𝒳.projection) hD𝒳 M)
            ↥(Deformation.tangentModuleAt.{u, u, u}
              (BasedCategory.ofFunctor D𝒵.projection) hD𝒵 M)) -
        (Deformation.tangentMapAt.{u, u, u} hD𝒵 hD𝒴
            ({ toFunctor := data.rightFunctor, w := data.rightFunctor_projection } :
              BasedCategory.ofFunctor D𝒵.projection ⥤ᵇ
                BasedCategory.ofFunctor D𝒴.projection) M).comp
          (LinearMap.snd k
            ↥(Deformation.tangentModuleAt.{u, u, u}
              (BasedCategory.ofFunctor D𝒳.projection) hD𝒳 M)
            ↥(Deformation.tangentModuleAt.{u, u, u}
              (BasedCategory.ofFunctor D𝒵.projection) hD𝒵 M))) := by
  intro hA hB hF hG hX hZ hY D𝒲 D𝒳 D𝒵 D𝒴 mA mB mF data hD𝒲 hD𝒳 hD𝒵 hD𝒴
  let := D𝒲.category
  let := D𝒳.category
  let := D𝒵.category
  let := D𝒴.category
  exact Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq.{u, u, u}
    D𝒴.projection D𝒳.projection D𝒵.projection D𝒲.projection
    mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor
    mF.projection_comm data.rightFunctor_projection
    mA.projection_comm mB.projection_comm data.filler data.filler_vertical
    data.isEquivalence hD𝒲 hD𝒳 hD𝒵 hD𝒴 M

/-- **Stacks Project, Tag 07X2**, the full six-term exact sequence.

Let `S` be a locally Noetherian scheme, let `Φ : 𝒳 ⟶ 𝒴` and `Ψ : 𝒵 ⟶ 𝒴` be `1`-morphisms
of categories fibred in groupoids over the big fppf site of `S`, and assume `𝒳`, `𝒴`, `𝒵`
satisfy (RS). Let `k` be a field of finite type over `S` and let `w₀` be an object of
`𝒲 = 𝒳 ×_𝒴 𝒵` over `k`, with induced objects `x₀`, `y₀ = Φ(x₀)`, `z₀` of `𝒳`, `𝒴`,
`𝒵`. Then

`0 → Inf(𝓕_𝒲) → Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵) → Inf(𝓕_𝒴) → T𝓕_𝒲 → T𝓕_𝒳 ⊕ T𝓕_𝒵 → T𝓕_𝒴`

is an exact sequence, with the first pair of maps induced by the two projections of `𝒲`, the
first difference by the maps induced by `Φ` and by `Ψ` (the latter transported along the
comparison isomorphism `ψ(w₀) : Φ(x₀) ≅ Ψ(z₀)`), a boundary map out of `Inf(𝓕_𝒴)`, and again
the pair of projections and the difference of the maps induced by `Φ` and `Ψ`, now on tangent
spaces.

The square of predeformation categories is a `2`-fibre product (Tag 07WL): the comparison
`1`-morphism from `𝒲` to `CategoryTheory.TwoFibreProductOver` is an equivalence
(`Deformation.Artin.fibreProductOfPredeformationCategoriesOfEssSurj`). Each of the five
exactness/injectivity claims of the abstract six-term sequence for the literal `2`-fibre product
(Tag 06L5, `Deformation.SixTerm.twoFibreProduct_sixTermExact`) is transported along this
equivalence, respectively by `Deformation.injective_infProjPairOfLift`,
`Deformation.exact_infProjPairOfLift`, `Deformation.exact_infLegDiff_infBoundaryLinearMapOfLift`,
`Deformation.exact_infBoundaryLinearMapOfLift_tangentProjPairOfLift` and
`Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq`. -/
@[stacks 07X2]
public theorem sixTermExact_twoFibreProduct
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
    letI := D𝒲.category
    letI := D𝒳.category
    letI := D𝒵.category
    letI := D𝒴.category
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
    letI := hlift'
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
    let PF' := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids
      hD𝒴.predeformation.cofibered (data.rightFunctor.obj (mB.toFunctor.obj w₀'.1))
    letI := Deformation.naturalLocalizedTangentAddCommGroup PW hD𝒲.satisfiesRS
    letI := Deformation.naturalLocalizedTangentModule PW hD𝒲.satisfiesRS
    letI := Deformation.naturalLocalizedTangentAddCommGroup QH hH'.satisfiesRS
    letI := Deformation.naturalLocalizedTangentModule QH hH'.satisfiesRS
    letI := Deformation.naturalLocalizedTangentAddCommGroup QG hG'.satisfiesRS
    letI := Deformation.naturalLocalizedTangentModule QG hG'.satisfiesRS
    letI := Deformation.naturalLocalizedTangentAddCommGroup PF hD𝒴.satisfiesRS
    letI := Deformation.naturalLocalizedTangentModule PF hD𝒴.satisfiesRS
    Function.Injective
      (LinearMap.prod
        (Deformation.inducedInfinitesimalLinearMapOfEq mA.toFunctor hA' hD𝒲.satisfiesRS
          hH'.satisfiesRS PW QH)
        (Deformation.inducedInfinitesimalLinearMapOfEq mB.toFunctor hB' hD𝒲.satisfiesRS
          hG'.satisfiesRS PW QG)) ∧
    Function.Exact
      (LinearMap.prod
        (Deformation.inducedInfinitesimalLinearMapOfEq mA.toFunctor hA' hD𝒲.satisfiesRS
          hH'.satisfiesRS PW QH)
        (Deformation.inducedInfinitesimalLinearMapOfEq mB.toFunctor hB' hD𝒲.satisfiesRS
          hG'.satisfiesRS PW QG))
      (Deformation.infLegDiff D𝒴.projection mF.toFunctor data.rightFunctor hH' hG' hD𝒴
        (w₀ :=
          (⟨D𝒲.projection.obj w₀'.1, mA.toFunctor.obj w₀'.1, mB.toFunctor.obj w₀'.1,
              Functor.congr_obj hA' w₀'.1, Functor.congr_obj hB' w₀'.1,
              data.filler.app w₀'.1, data.filler_vertical w₀'.1⟩ :
            TwoFibreProductOver (mF.toFunctor ⋙ D𝒴.projection)
              (data.rightFunctor ⋙ D𝒴.projection) D𝒴.projection mF.toFunctor
              data.rightFunctor))
        QH QG PF PF' hw₀) ∧
    Function.Exact
      (Deformation.infLegDiff D𝒴.projection mF.toFunctor data.rightFunctor hH' hG' hD𝒴
        (w₀ :=
          (⟨D𝒲.projection.obj w₀'.1, mA.toFunctor.obj w₀'.1, mB.toFunctor.obj w₀'.1,
              Functor.congr_obj hA' w₀'.1, Functor.congr_obj hB' w₀'.1,
              data.filler.app w₀'.1, data.filler_vertical w₀'.1⟩ :
            TwoFibreProductOver (mF.toFunctor ⋙ D𝒴.projection)
              (data.rightFunctor ⋙ D𝒴.projection) D𝒴.projection mF.toFunctor
              data.rightFunctor))
        QH QG PF PF' hw₀)
      (Deformation.infBoundaryLinearMapOfLift D𝒴.projection D𝒲.projection mF.toFunctor
        data.rightFunctor mA.toFunctor mB.toFunctor hA' hB' data.filler data.filler_vertical
        hlift' hD𝒲 hH' hG' hD𝒴 QH QG PF) ∧
    Function.Exact
      (Deformation.infBoundaryLinearMapOfLift D𝒴.projection D𝒲.projection mF.toFunctor
        data.rightFunctor mA.toFunctor mB.toFunctor hA' hB' data.filler data.filler_vertical
        hlift' hD𝒲 hH' hG' hD𝒴 QH QG PF)
      (LinearMap.prod
        (Deformation.tangentMapAt hD𝒲 hH'
          ({ toFunctor := mA.toFunctor, w := hA' } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection))
          (FGModuleCat.of k (ULift.{u} k)))
        (Deformation.tangentMapAt hD𝒲 hG'
          ({ toFunctor := mB.toFunctor, w := hB' } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection))
          (FGModuleCat.of k (ULift.{u} k)))) ∧
    Function.Exact
      (LinearMap.prod
        (Deformation.tangentMapAt hD𝒲 hH'
          ({ toFunctor := mA.toFunctor, w := hA' } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection))
          (FGModuleCat.of k (ULift.{u} k)))
        (Deformation.tangentMapAt hD𝒲 hG'
          ({ toFunctor := mB.toFunctor, w := hB' } :
            BasedCategory.ofFunctor D𝒲.projection ⥤ᵇ
              BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection))
          (FGModuleCat.of k (ULift.{u} k))))
      ((Deformation.tangentMapAt hH' hD𝒴
            ({ toFunctor := mF.toFunctor, w := rfl } :
              BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection) ⥤ᵇ
                BasedCategory.ofFunctor D𝒴.projection)
            (FGModuleCat.of k (ULift.{u} k))).comp
          (LinearMap.fst k
            ↥(Deformation.tangentModuleAt
              (BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection)) hH'
              (FGModuleCat.of k (ULift.{u} k)))
            ↥(Deformation.tangentModuleAt
              (BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection)) hG'
              (FGModuleCat.of k (ULift.{u} k)))) -
        (Deformation.tangentMapAt hG' hD𝒴
            ({ toFunctor := data.rightFunctor, w := rfl } :
              BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection) ⥤ᵇ
                BasedCategory.ofFunctor D𝒴.projection)
            (FGModuleCat.of k (ULift.{u} k))).comp
          (LinearMap.snd k
            ↥(Deformation.tangentModuleAt
              (BasedCategory.ofFunctor (mF.toFunctor ⋙ D𝒴.projection)) hH'
              (FGModuleCat.of k (ULift.{u} k)))
            ↥(Deformation.tangentModuleAt
              (BasedCategory.ofFunctor (data.rightFunctor ⋙ D𝒴.projection)) hG'
              (FGModuleCat.of k (ULift.{u} k))))) := by
  intro hA hB hF hG hX hZ hY D𝒲 D𝒳 D𝒵 D𝒴 mA mB mF data hD𝒲 hD𝒳 hD𝒵 hD𝒴 hA' hB' hH' hG'
    hlift' w₀' hw₀ PW QH QG PF PF'
  let := D𝒲.category
  let := D𝒳.category
  let := D𝒵.category
  let := D𝒴.category
  let := hlift'
  let PL := Deformation.transportChosenPushforwardsAt
    (TwoFibreProductOver.lift (mF.toFunctor ⋙ D𝒴.projection)
      (data.rightFunctor ⋙ D𝒴.projection) D𝒴.projection mF.toFunctor data.rightFunctor
      D𝒲.projection mA.toFunctor mB.toFunctor hA' hB' data.filler data.filler_vertical)
    (TwoFibreProductOver.lift_comp_structureFunctor ..) w₀'.1 PW
  let := Deformation.naturalLocalizedTangentAddCommGroup PW hD𝒲.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule PW hD𝒲.satisfiesRS
  let := Deformation.naturalLocalizedTangentAddCommGroup QH hH'.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule QH hH'.satisfiesRS
  let := Deformation.naturalLocalizedTangentAddCommGroup QG hG'.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule QG hG'.satisfiesRS
  let := Deformation.naturalLocalizedTangentAddCommGroup PF hD𝒴.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule PF hD𝒴.satisfiesRS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Deformation.injective_infProjPairOfLift D𝒴.projection
      (mF.toFunctor ⋙ D𝒴.projection) (data.rightFunctor ⋙ D𝒴.projection) D𝒲.projection
      mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor rfl rfl hA' hB'
      data.filler data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 PW QH QG PL
  · exact Deformation.exact_infProjPairOfLift D𝒴.projection D𝒲.projection
      mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor hA' hB' data.filler
      data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 PW QH QG PL PF PF' hw₀
  · exact Deformation.exact_infLegDiff_infBoundaryLinearMapOfLift D𝒴.projection D𝒲.projection
      mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor hA' hB' data.filler
      data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 PL QH QG PF PF' hw₀
  · exact Deformation.exact_infBoundaryLinearMapOfLift_tangentProjPairOfLift D𝒴.projection
      D𝒲.projection mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor hA' hB'
      data.filler data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 QH QG PF
  · exact Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq D𝒴.projection
      (mF.toFunctor ⋙ D𝒴.projection) (data.rightFunctor ⋙ D𝒴.projection) D𝒲.projection
      mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor rfl rfl hA' hB'
      data.filler data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴
      (FGModuleCat.of k (ULift.{u} k))

end TangentSpace

end Deformation.Artin

end
