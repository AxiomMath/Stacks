module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChartPoint
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice
public import StacksFrontier.Deformation.Artin.SliceTangentSpace
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.Versality.RepresentablySmoothPredeformation
public import StacksFrontier.Deformation.Artin.Versality.Openness

/-!
# The tangent space at a point of a category with a smooth chart (the reduction of Stacks 07X1)

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, satisfying (RS), with a 1-morphism `f : (Sch/V) ⟶ 𝒳` from the category represented by a
scheme, representable by algebraic spaces with surjective smooth base changes. Stacks 07X1
shows that the tangent space `T𝓕_{𝒳,k,x₀}` is finite-dimensional as follows. A point `u₀` of
`(Sch/V)` over a finite extension `l/k` maps to the restriction `x_{l,0}` of `x₀`; the change of
residue field `(𝓕_{𝒳,k,x₀})_{l/k}` is `𝓕_{𝒳,l,x_{l,0}}` (Stacks 07WX), so by Stacks 07WB it is
enough to bound `T𝓕_{𝒳,l,x_{l,0}}`; the functor `𝓕_{(Sch/V),l,u₀} ⟶ 𝓕_{𝒳,l,x_{l,0}}` is smooth
(Stacks 07WK), so the tangent map is surjective (Stacks 06HN, 06IJ), and `T𝓕_{(Sch/V),l,u₀}` is
finite-dimensional.

Here Stacks 07WX over the big fppf site is
`Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence`, Stacks 07WK at the chart is
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`, and the
finite-dimensionality of `T𝓕_{(Sch/V),l,u₀}` is `Deformation.Artin.SliceTangent`. Condition (RS)
for `𝒳` is a hypothesis: for an algebraic stack it is Stacks 07WQ.

## Main results

* `Deformation.Artin.locallyOfFiniteType_quasiCompact_of_finite`: a finite extension of a field of
  finite type over `S` is of finite type over `S`.
* `Deformation.Artin.finiteDimensional_tangentModuleAt_slice`: the tangent space of a point of a
  scheme locally of finite type over `S` is finite-dimensional.
* `Deformation.Artin.finiteDimensional_tangentModuleAt_of_smoothChart`: the tangent space
  `T𝓕_{𝒳,k,x₀}` of a category satisfying (RS) with a smooth chart is finite-dimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- A finite extension of a field of finite type over `S` is of finite type over `S`. -/
theorem locallyOfFiniteType_quasiCompact_of_finite {S : Scheme.{u}} {Λ k l : Type u}
    [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l] (iΛ : Spec (.of Λ) ⟶ S)
    (h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := by
  obtain ⟨h1, h2⟩ := h
  have he : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
    rw [IsScalarTower.algebraMap_eq Λ k l, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k l))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The tangent space of a point of a scheme locally of finite type over `S`, read in the tangent
module `Deformation.tangentModuleAt`, is finite-dimensional. -/
theorem finiteDimensional_tangentModuleAt_slice (V : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] (iΛ : Spec (.of Λ) ⟶ S)
    [IsOpenImmersion iΛ] (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)) :
    FiniteDimensional l ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (Over.forget V ⋙ Over.post B.inclusion) u₀ hu₀).projection)
      (isDeformationCategory_predeformationCategory B S hS (Over.forget V)
        (Functor.IsFiberedInGroupoids.over_forget V) (satisfiesRS_over_forget B S hS V) iΛ u₀
        hu₀ hfin.1 hfin.2)
      (FGModuleCat.of l l)) := by
  have hp := isDeformationCategory_predeformationCategory B S hS (Over.forget V)
    (Functor.IsFiberedInGroupoids.over_forget V) (satisfiesRS_over_forget B S hS V) iΛ u₀
    hu₀ hfin.1 hfin.2
  exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hp).mp
    (SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased hp.predeformation
      (tangentConditionS2 hp))

/-- Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, satisfying (RS), with a 1-morphism `f : (Sch/V) ⟶ 𝒳` representable by algebraic
spaces whose base changes are surjective and smooth. Then the tangent space of `𝓕_{𝒳,k,x₀}` is
finite-dimensional, for every field `k` of finite type over `S` and every affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with `Λ → k` finite. -/
theorem finiteDimensional_tangentModuleAt_of_smoothChart [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (V : BigFppfOver B S hS) (f : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (W : BigFppfOver B S hS)
      (yv : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map W.hom)
      (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B W.left.1 W.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom) (Stack.schemeFibredCategory B S hS V).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS W
        ((spacesOverSmallerBaseFunctor B W.left.1 S W.left.2 hS W.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
      (isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids hRS
        iΛ x₀ hx₀ hfinite.1 hfinite.2)
      (FGModuleCat.of k k)) := by
  have : IsOpenImmersion iΛ := hiΛ
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  obtain ⟨l, _, _, _, _, hkl, u₀, hu₀, hxₗ, η, hηbase⟩ :=
    exists_finite_extension_chart_point 𝒳 V f hf hprop iΛ x₀ hx₀
  have : Module.Finite Λ l := Module.Finite.trans k l
  let T : ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := l }
  have hfinl := locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := l) iΛ hfinite
  let q := 𝒳.val.p ⋙ Over.post B.inclusion
  let D₀ := predeformationCategory iΛ q x₀ hx₀
  let Dₗ := predeformationCategory iΛ q ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ
  let := D₀.category
  let := Dₗ.category
  have hD₀ := isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
    hRS iΛ x₀ hx₀ hfinite.1 hfinite.2
  have hDₗ := isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
    hRS iΛ ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ hfinl.1 hfinl.2
  have hcart : 𝒳.val.p.IsCartesian (𝒳.val.p.map η) η := by
    have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝒳.val.p.map η) η
    infer_instance
  let C := Site.changeOfFieldFunctor T iΛ B hS 𝒳.val.p x₀ _ hx₀ hxₗ η 𝒳.isFiberedInGroupoids
    hcart hηbase
  let F := C.toFunctor
  have hFcomm := C.projection_comm
  have hFeq : F.IsEquivalence := Site.changeOfFieldFunctor_isEquivalence T iΛ B hS 𝒳.val.p x₀ _
    hx₀ hxₗ η 𝒳.isFiberedInGroupoids hcart hηbase hfinite hRS
  have hG : IsDeformationCategory (changeOfFieldsProjection.{u, u, u, u} T D₀.projection) :=
    ⟨changeOfFieldsProjection_isPredeformationCategory T D₀.projection hD₀.predeformation,
      changeOfFieldsProjection_satisfiesRS T D₀.projection hD₀.satisfiesRS⟩
  have hDU := isDeformationCategory_predeformationCategory B S hS (Over.forget V)
    (Functor.IsFiberedInGroupoids.over_forget V) (satisfiesRS_over_forget B S hS V) iΛ u₀ hu₀
    hfinl.1 hfinl.2
  have hUfin := finiteDimensional_tangentModuleAt_slice V iΛ u₀ hu₀ hfinl
  have hsm : IsSmoothOnPredeformationCategories B S hS
      (Stack.schemeFibredCategory B S hS V).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f) :=
    Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth' B S hS f
      ⟨hf, fun W y hy F hF he => (hprop W y hy F hF he).2⟩
  have hsmooth := hsm iΛ u₀ hu₀ hfinl.1 hfinl.2 hiΛ
  have hlfin : FiniteDimensional l ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor Dₗ.projection) hDₗ (FGModuleCat.of l l)) :=
    finiteDimensional_tangentModuleAt_of_isSmooth hDU hDₗ _ hsmooth _ hUfin
  let Φ : BasedCategory.ofFunctor (changeOfFieldsProjection.{u, u, u, u} T D₀.projection) ⥤ᵇ
      BasedCategory.ofFunctor Dₗ.projection := ⟨F, hFcomm⟩
  have : Φ.toFunctor.Full := hFeq.full
  have : Φ.toFunctor.Faithful := hFeq.faithful
  have hGfin := finiteDimensional_tangentModuleAt_of_fullyFaithful hG hDₗ Φ _ hlfin
  exact finiteDimensional_tangentModuleAt_of_changeOfFields T
    (BasedCategory.ofFunctor D₀.projection) hD₀ hG hGfin

end Deformation.Artin
