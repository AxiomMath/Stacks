module

public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.Deformation.Artin.AlgebraicStackTangentSpace
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.ChangeOfFields

/-!
# Deformation categories of algebraic stacks are finite dimensional

Let `S` be a locally Noetherian scheme, `𝒳` an algebraic stack over `S`, `U` a scheme locally
of finite type over `S` with a smooth surjective 1-morphism `(Sch/U) ⟶ 𝒳`, and `x₀` an object
of `𝒳` over a field `k` of finite type over `S`. This file proves Tag 07X1: the deformation
category `𝓕 = 𝓕_{𝒳,k,x₀}` of Tag 07T2 has finite dimensional tangent space and finite
dimensional space of infinitesimal automorphisms.

The tangent space is treated in `StacksFrontier.Deformation.Artin.AlgebraicStackTangentSpace`.
For the infinitesimal automorphisms, choose a finite extension `l / k` and a point `u₀` of `U`
over `l` lifting `x₀`. By Tag 07WC, `Inf(𝓕) ⊗_k l` is the space of infinitesimal
automorphisms of `𝓕_{l/k}`, which injects into `Inf(𝓕_{𝒳,l,x_{l,0}})` because the canonical
functor of Tag 07WX is faithful (Tag 07W6). Let `𝓡 = (Sch/U) ×_𝒳 (Sch/U)`, an algebraic
stack by Tag 04TF. The six-term sequence of Tag 07X2 for this 2-fibre product, at the point
`(u₀, u₀, id)`, and the vanishing of infinitesimal automorphisms of points of schemes, embed
`Inf(𝓕_{𝒳,l,x_{l,0}})` linearly into the tangent space of `𝓡`, which is finite dimensional
because `𝓡` has a smooth surjective presentation by a scheme smooth over `U`.

## Main results

* `Deformation.Artin.isFiniteDimensionalDeformationCategory_of_isAlgebraicStack`: Tag 07X1.
* `Deformation.Artin.finiteDimensional_localizedAutomorphismFunctorTangent_of_chartPoint`: the
  infinitesimal automorphisms at a point lifting to the presentation are finite dimensional.
* `Deformation.Artin.exists_presentation_twoFibreProductAlgebraicStack`: a presentation of
  `(Sch/U) ×_𝒳 (Sch/U)` by a scheme locally of finite type over `S`.

## Implementation notes

That finite dimensionality of infinitesimal automorphisms pulls back along a faithful morphism
(Tag 07W6) and descends along a change of fields (Tag 07WC) is
`Deformation.finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful` and
`Deformation.finiteDimensional_localizedAutomorphismFunctorTangent_of_changeOfFields`.

As in the source, `(𝓕_{𝒳,k,x₀})_{l/k} = 𝓕_{𝒳,l,x_{l,0}}` is deduced from condition (RS) for
`𝒳` (Tag 07WQ, `Deformation.Artin.satisfiesRS_of_isAlgebraicStack`); only the faithfulness of
the canonical functor is used. The deformation categories involved are deformation categories by
condition (RS) at the squares inducing surjections on residue fields
(`Deformation.Artin.satisfiesRSOfResidue_of_isAlgebraicStack`).

The presentation `(Sch/U) ⟶ 𝒳` is a 1-morphism of algebraic stacks, smooth in the sense of
Tag 075U and surjective in the sense of Tag 04ZS. As in the source, that it is representable by
algebraic spaces is not assumed: it follows from the representability of the diagonal of `𝒳`
(Tag 045G). This is where the statement differs from
`Deformation.Artin.isFiniteDimensionalDeformationCategory_of_algebraicStack`, which assumes the
representability and states smoothness and surjectivity for the representable 1-morphism.

## References

* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
* [Stacks Project, Tag 07X2](https://stacks.math.columbia.edu/tag/07X2)
* [Stacks Project, Tag 07WC](https://stacks.math.columbia.edu/tag/07WC)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u w

namespace Deformation

section Infinitesimal

universe v u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Points with thin fibres over the dual numbers have no infinitesimal automorphisms.** -/
theorem subsingleton_localizedAutomorphismFunctorTangent
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
    (P : ChosenPushforwardsAt p x)
    (h : Quiver.IsThin (p.Fiber (dualNumbersUnder (p := p) (x := x)).right)) :
    Subsingleton (localizedAutomorphismFunctorTangent P) := by
  have : Subsingleton (infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x))) :=
    ⟨fun a b => Subtype.ext (Iso.ext ((h _ _).elim _ _))⟩
  exact (localizedTangentEquivKernel P).injective.subsingleton

/-- The tangent module at the rank-one module of a deformation category is finite
dimensional as soon as its tangent space is, in the model of `Deformation.artinianTangentSpace`. -/
theorem finiteDimensional_tangentModuleAt_of_artinianTangentSpace {Λ k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k] (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{w, w, w} Λ k))
    (h : IsDeformationCategory.{w, w, w} 𝓕.p)
    (hfd :
      letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h.predeformation⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓕 h.predeformation.cofibered))) :=
        ⟨tangentConditionS2 h⟩
      FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕
        h.predeformation.cofibered))) :
    FiniteDimensional k (tangentModuleAt.{w, w, w} 𝓕 h (FGModuleCat.of k (ULift.{w} k))) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h.predeformation.cofibered))) :=
    ⟨tangentConditionS2 h⟩
  have h1 := finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓕 h.predeformation
    (tangentConditionS2 h) hfd
  exact (associatedTangentSpaceCarrierLinearEquiv.{w, w, w} 𝓕 h.predeformation
    (tangentConditionS2 h)).symm.finiteDimensional

end Infinitesimal

end Deformation

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth surjective presentation of the self 2-fibre product of a presentation.** If
`(Sch/U) ⟶ 𝒳` is smooth and surjective, the 2-fibre product `(Sch/U) ×_𝒳 (Sch/U)` has a smooth
surjective presentation by a scheme which is smooth over `U`, hence locally of finite type over
`S` when `U` is. -/
theorem exists_presentation_twoFibreProductAlgebraicStack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsurj : Stack.IsSurjective B S hS a) (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a) :
    ∃ (V : BigFppfOver B S hS) (_ : LocallyOfFiniteType (B.inclusion.map V.hom))
      (c : Stack.schemeStack.{u, w} B S hS V ⟶ Stack.twoFibreProductAlgebraicStack B S hS a a),
      Stack.IsSurjective B S hS c ∧ Stack.AlgebraicStacks.IsSmooth B S hS c := by
  let P := Stack.twoFibreProductSquareAlgebraicStacks B S hS a a
  have hP : Bicategory.IsTwoFibreProduct P :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a a
  have hPsurj : Stack.IsSurjective B S hS P.fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsurj
  have hPsm : Stack.AlgebraicStacks.IsSmooth B S hS P.fst :=
    Stack.AlgebraicStacks.isSmooth_baseChange B S hS a a P hP hsm
  obtain ⟨V, c, hcsm, hcsurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwsurj : Stack.IsSurjective B S hS (c ≫ P.fst) :=
    Stack.isSurjective_comp B S hS c P.fst hcsurj hPsurj
  have hwsm : Stack.AlgebraicStacks.IsSmooth B S hS (c ≫ P.fst) :=
    Stack.AlgebraicStacks.isSmooth_comp B S hS c P.fst hcsm hPsm
  obtain ⟨q, hqsm, -, -⟩ :=
    Stack.exists_schemeMap_of_isSurjective_isSmooth B S hS (c ≫ P.fst) hwsurj hwsm
  have hV : LocallyOfFiniteType (B.inclusion.map V.hom) := by
    have : Smooth (B.inclusion.map q.left) := hqsm
    rw [← Over.w q, Functor.map_comp]
    infer_instance
  exact ⟨V, hV, c, hcsurj, hcsm⟩

/-- **Infinitesimal automorphisms at a point lifting to a presentation are finite
dimensional.** For a point `u₀` of a scheme `U` locally of finite type over `S` over a field
`l`, with a smooth surjective 1-morphism `(Sch/U) ⟶ 𝒳`, the infinitesimal automorphisms of
every object of the special fibre of `𝓕_{𝒳,l,x_{l,0}}` form a finite dimensional `l`-vector
space. The six-term sequence of Tag 07X2 for `𝓡 = (Sch/U) ×_𝒳 (Sch/U)` at `(u₀, u₀, id)`
embeds them into the tangent space of `𝓡`, since points of schemes have no infinitesimal
automorphisms, and `𝓡` is an algebraic stack (Tag 04TF) with a presentation by a scheme
locally of finite type over `S`. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_chartPoint
    [IsLocallyNoetherian S]
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsurj : Stack.IsSurjective B S hS a) (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] [Module.Finite Λ l]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (u₀ : Over U)
    (hu₀ : (Over.forget U ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hxₗ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj
        ((CatFiberedInGroupoids.homFunctor a.hom).obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)) :
    let D := predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion)
      ((CatFiberedInGroupoids.homFunctor a.hom).obj u₀) hxₗ
    letI := D.category
    let hD : IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ _ hxₗ
        hfinite hqc
    ∀ (y : D.carrier), D.projection.obj y = residueFieldObject.{u, u, u} Λ l →
      ∀ P : ChosenPushforwardsAt D.projection y,
        letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
        letI := naturalLocalizedTangentModule P hD.satisfiesRS
        FiniteDimensional l (localizedAutomorphismFunctorTangent P) := by
  intro D hD y hy P
  let := D.category
  let pU := (Stack.schemeStack.{u, w} B S hS U).val.val.p
  let pX := 𝒳.val.val.p
  let Φ := CatFiberedInGroupoids.homFunctor a.hom
  have hΦ : Φ ⋙ pX = pU := CatFiberedInGroupoids.homFunctor_comp_p a.hom
  let w₀ : TwoFibreProductOver pU pU pX Φ Φ :=
    { base := pU.obj u₀
      x := u₀
      y := u₀
      hx := rfl
      hy := rfl
      iso := Iso.refl _
      vertical := CategoryTheory.IsHomLift.id (Functor.congr_obj hΦ u₀) }
  have hw₀base : (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙
      Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := hu₀
  -- the tangent space of `𝓡 = (Sch/U) ×_𝒳 (Sch/U)` at `w₀` is finite dimensional
  let R := Stack.twoFibreProductAlgebraicStack B S hS a a
  obtain ⟨V, hV, c, hcsurj, hcsm⟩ :=
    exists_presentation_twoFibreProductAlgebraicStack B S hS 𝒳 U a hsurj hsm
  have := hV
  have hTR := finiteDimensional_artinianTangentSpace_of_isAlgebraicStack B S hS R V c hcsurj hcsm
    iΛ (w₀ : R.val.val.obj) hw₀base hfinite hqc
  -- the square of predeformation categories of Tag 07WL
  let hA := fst_comp_post_eq B S hS pU pX pU Φ Φ
  let hB := snd_comp_post_eq B S hS pU pX pU Φ Φ
  let hF : Φ ⋙ pX ⋙ Over.post B.inclusion = pU ⋙ Over.post B.inclusion :=
    congrArg (fun H => H ⋙ Over.post B.inclusion) hΦ
  let hX := imageBasePoint (qY := pU ⋙ Over.post B.inclusion) iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion)
    (TwoFibreProductOver.fst pU pU pX Φ Φ) hA w₀ hw₀base
  let hZ := imageBasePoint (qY := pU ⋙ Over.post B.inclusion) iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion)
    (TwoFibreProductOver.snd pU pU pX Φ Φ) hB w₀ hw₀base
  let D𝒲 := predeformationCategory iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion) w₀ hw₀base
  let D𝒳 := predeformationCategory iΛ (pU ⋙ Over.post B.inclusion)
    ((TwoFibreProductOver.fst pU pU pX Φ Φ).obj w₀) hX
  let D𝒵 := predeformationCategory iΛ (pU ⋙ Over.post B.inclusion)
    ((TwoFibreProductOver.snd pU pU pX Φ Φ).obj w₀) hZ
  let := D𝒲.category
  let := D𝒳.category
  let := D𝒵.category
  let mA := mapPredeformationCategory iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion)
    (pU ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst pU pU pX Φ Φ) hA w₀ hw₀base
  let mB := mapPredeformationCategory iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion)
    (pU ⋙ Over.post B.inclusion) (TwoFibreProductOver.snd pU pU pX Φ Φ) hB w₀ hw₀base
  let mF := mapPredeformationCategory iΛ (pU ⋙ Over.post B.inclusion)
    (pX ⋙ Over.post B.inclusion) Φ hF ((TwoFibreProductOver.fst pU pU pX Φ Φ).obj w₀) hX
  let data := fibreProductOfPredeformationCategoriesOfEssSurj iΛ
    (TwoFibreProductOver.structureFunctor pU pU pX Φ Φ ⋙ Over.post B.inclusion)
    (pU ⋙ Over.post B.inclusion) (pU ⋙ Over.post B.inclusion)
    (pX ⋙ Over.post B.inclusion) (TwoFibreProductOver.fst pU pU pX Φ Φ)
    (TwoFibreProductOver.snd pU pU pX Φ Φ) Φ Φ hA hB hF
    (TwoFibreProductOver.psiIso pU pU pX Φ Φ) w₀ hw₀base hF
    (isHomLift_psiIso_post B S hS pU pX pU Φ Φ)
    (exists_liftPost_iso_over_base B S hS pU pX pU Φ Φ)
    (isEquivalence_liftPost B S hS pU pX pU Φ Φ)
  let hY := imageBasePoint (qY := pX ⋙ Over.post B.inclusion) iΛ
    (pU ⋙ Over.post B.inclusion) Φ hF ((TwoFibreProductOver.fst pU pU pX Φ Φ).obj w₀) hX
  let D𝒴 := predeformationCategory iΛ (pX ⋙ Over.post B.inclusion)
    (Φ.obj ((TwoFibreProductOver.fst pU pU pX Φ Φ).obj w₀)) hY
  let := D𝒴.category
  let hD𝒴 : IsDeformationCategory D𝒴.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ _ hY
      hfinite hqc
  let hD𝒲 : IsDeformationCategory D𝒲.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS R iΛ w₀ hw₀base
      hfinite hqc
  let hD𝒳 : IsDeformationCategory D𝒳.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS
      (Stack.schemeStack.{u, w} B S hS U) iΛ _ hX hfinite hqc
  let hD𝒵 : IsDeformationCategory D𝒵.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS
      (Stack.schemeStack.{u, w} B S hS U) iΛ _ hZ hfinite hqc
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
  let w₀' : D𝒲.projection.Fiber (Deformation.residueFieldObject Λ l) :=
    (Classical.choice hD𝒲.predeformation.specialFiber).inverse.obj ⟨PUnit.unit⟩
  let hw₀ : (mF.toFunctor ⋙ D𝒴.projection).obj (mA.toFunctor.obj w₀'.1) =
      Deformation.residueFieldObject Λ l :=
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
  let PL := Deformation.transportChosenPushforwardsAt
    (TwoFibreProductOver.lift (mF.toFunctor ⋙ D𝒴.projection)
      (data.rightFunctor ⋙ D𝒴.projection) D𝒴.projection mF.toFunctor data.rightFunctor
      D𝒲.projection mA.toFunctor mB.toFunctor hA' hB' data.filler data.filler_vertical)
    (TwoFibreProductOver.lift_comp_structureFunctor ..) w₀'.1 PW
  let := Deformation.naturalLocalizedTangentAddCommGroup QH hH'.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule QH hH'.satisfiesRS
  let := Deformation.naturalLocalizedTangentAddCommGroup QG hG'.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule QG hG'.satisfiesRS
  let := Deformation.naturalLocalizedTangentAddCommGroup PF hD𝒴.satisfiesRS
  let := Deformation.naturalLocalizedTangentModule PF hD𝒴.satisfiesRS
  have habs := Deformation.exact_infLegDiff_infBoundaryLinearMapOfLift D𝒴.projection
    D𝒲.projection mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor hA' hB' data.filler
    data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 PL QH QG PF PF' hw₀
  -- points of schemes have no infinitesimal automorphisms
  have hthin : ∀ {v : Over U} (hv) (A : ArtinianLocalAlgCat.{u, u, u} Λ l),
      Quiver.IsThin ((SliceTangent.sliceDeformations iΛ v hv).projection.Fiber A) :=
    fun _ _ y y' => SliceTangent.subsingleton_fiber_hom (iΛ := iΛ) y y'
  have := subsingleton_localizedAutomorphismFunctorTangent QH
    (mF.projection_comm ▸ hthin hX _)
  have := subsingleton_localizedAutomorphismFunctorTangent QG
    (data.rightFunctor_projection ▸ hthin hZ _)
  -- hence the boundary map into the tangent space of `𝓡` is injective
  have hinj : Function.Injective (Deformation.infBoundaryLinearMapOfLift D𝒴.projection
      D𝒲.projection mF.toFunctor data.rightFunctor mA.toFunctor mB.toFunctor hA' hB'
      data.filler data.filler_vertical hlift' hD𝒲 hH' hG' hD𝒴 QH QG PF) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨z, hz⟩ := (habs m).1 hm
    rw [← hz, Subsingleton.elim z 0, map_zero]
  have hTR' : FiniteDimensional l (tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor D𝒲.projection)
      hD𝒲 (FGModuleCat.of l (ULift.{u} l))) :=
    finiteDimensional_tangentModuleAt_of_artinianTangentSpace _ hD𝒲 hTR
  have : FiniteDimensional l (localizedAutomorphismFunctorTangent PF) :=
    Module.Finite.of_injective _ hinj
  -- every other point of the special fibre has isomorphic infinitesimal automorphisms
  let x₁ : D𝒴.carrier := mF.toFunctor.obj (mA.toFunctor.obj w₀'.1)
  let y' : D𝒴.carrier := y
  let P' : ChosenPushforwardsAt D𝒴.projection y' := P
  obtain ⟨jiso, -⟩ := existsUnique_pointIso hD𝒴.predeformation
    (⟨y', hy⟩ : D𝒴.projection.Fiber (residueFieldObject.{u, u, u} Λ l)) ⟨x₁, hw₀⟩
  let := naturalLocalizedTangentAddCommGroup P' hD𝒴.satisfiesRS
  let := naturalLocalizedTangentModule P' hD𝒴.satisfiesRS
  exact (canonicalLocalizedTangentAutomorphismLinearEquiv hD𝒴.satisfiesRS jiso.hom.1 hw₀ P'
    PF).symm.finiteDimensional

/-- **Stacks Project, Tag 07X1.** Let `S` be a locally Noetherian scheme, `𝒳` an algebraic
stack over `S`, `U` a scheme locally of finite type over `S`, and `(Sch/U) ⟶ 𝒳` a smooth
surjective 1-morphism. For every deformation category `𝓕 = 𝓕_{𝒳,k,x₀}` of Tag 07T2 — a point
`x₀` of `𝒳` over a field `k` of finite type over `S`, and an affine open `Spec Λ ⊂ S` through
which `Spec k ⟶ S` factors with `Λ ⟶ k` finite — the tangent space `T𝓕` and the space of
infinitesimal automorphisms `Inf(𝓕)` are finite dimensional over `k`. -/
@[stacks 07X1]
theorem isFiniteDimensionalDeformationCategory_of_isAlgebraicStack [IsLocallyNoetherian S]
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsurj : Stack.IsSurjective B S hS a) (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    IsFiniteDimensionalDeformationCategory D.projection := by
  intro D
  let := D.category
  have hD : IsDeformationCategory D.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ x₀ hx₀
      hfinite hqc
  refine ⟨hD, ?_, ?_⟩
  · exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace
      (BasedCategory.ofFunctor D.projection) hD.predeformation (tangentConditionS2 hD)
      (finiteDimensional_artinianTangentSpace_of_isAlgebraicStack B S hS 𝒳 U a hsurj hsm iΛ x₀
        hx₀ hfinite hqc)
  intro x hx PF
  let := naturalLocalizedTangentAddCommGroup PF hD.satisfiesRS
  let := naturalLocalizedTangentModule PF hD.satisfiesRS
  suffices h : FiniteDimensional k (localizedAutomorphismFunctorTangent PF) from
    (tangentCarrierLinearEquiv PF hD.satisfiesRS).symm.finiteDimensional
  -- a point of the presentation over a finite extension `l / k`
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  obtain ⟨l, _, _, _, u₀, hu₀, hxₗ, η, hηbase⟩ :=
    exists_chartPoint B S hS 𝒳 U a hsurj hsm iΛ x₀ hx₀
  let : Algebra Λ l := ((algebraMap k l).comp (algebraMap Λ k)).toAlgebra
  have : IsScalarTower Λ k l := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite Λ l := Module.Finite.trans k l
  let T : ChangeOfFieldsSituation.{u, u, u} := ⟨Λ, k, l⟩
  obtain ⟨hfinl, hqcl⟩ := locallyOfFiniteType_quasiCompact_extendedPoint S T iΛ hfinite hqc
  let p := 𝒳.val.val.p
  let hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let xₗ := (CatFiberedInGroupoids.homFunctor a.hom).obj u₀
  let Dₗ := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ
  let := Dₗ.category
  have hDₗ : IsDeformationCategory Dₗ.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ xₗ hxₗ
      hfinl hqcl
  -- the faithful change of fields functor `𝓕_{l/k} ⟶ 𝓕_{𝒳,l,x_{l,0}}` of Tag 07WX
  have hη : p.IsCartesian (p.map η) η := by
    have := hp.isStronglyCartesian_homLift (p.map η) η
    infer_instance
  let G := Site.changeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
  have : G.toFunctor.IsEquivalence :=
    Site.changeOfFieldFunctor_isEquivalence T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
      ⟨hfinite, hqc⟩ (satisfiesRS_of_isAlgebraicStack B S hS 𝒳)
  -- a point of the special fibre of `𝓕_{l/k}`
  have hq := changeOfFieldsProjection_isPredeformationCategory T D.projection hD.predeformation
  let z : (changeOfFieldsProjection T D.projection).Fiber
      (residueFieldObject.{u, u, u} T.Λ T.l) :=
    (Classical.choice hq.specialFiber).inverse.obj ⟨PUnit.unit⟩
  let Q := chosenPushforwardsAtOfCofiberedInGroupoids hq.cofibered z.1
  let Q' := chosenPushforwardsAtOfCofiberedInGroupoids hDₗ.predeformation.cofibered
    (G.toFunctor.obj z.1)
  have hz : Dₗ.projection.obj (G.toFunctor.obj z.1) = residueFieldObject.{u, u, u} T.Λ T.l :=
    (Functor.congr_obj G.projection_comm z.1).trans z.2
  have hQ' := finiteDimensional_localizedAutomorphismFunctorTangent_of_chartPoint B S hS 𝒳 U a
    hsurj hsm iΛ hfinl hqcl u₀ hu₀ hxₗ (G.toFunctor.obj z.1) hz Q'
  exact finiteDimensional_localizedAutomorphismFunctorTangent_of_changeOfFields T D.projection hD
    ⟨x, hx⟩ PF z Q
    (finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful G.toFunctor
      G.projection_comm (changeOfFieldsProjection_satisfiesRS T D.projection hD.satisfiesRS)
      hDₗ.satisfiesRS Q Q' hQ')

end Deformation.Artin

end
