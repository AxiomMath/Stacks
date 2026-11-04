module

public import StacksFrontier.AlgebraicGeometry.Etale.SmoothCoverClosedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaDiagonalToProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SpecializationSmoothChart
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicStackEssSurj
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
public import StacksFrontier.Deformation.Artin.SliceTangentSpace
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation
public import StacksFrontier.Deformation.LiftsOfObjects.Smoothness.Criterion
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.VersalObject.ChangeOfFieldsTangentSpace

/-!
# The tangent space at a point of an algebraic stack is finite dimensional

Let `S` be a locally Noetherian scheme, `𝒳` an algebraic stack over `S` with a smooth surjective
presentation `(Sch/U) ⟶ 𝒳` by a scheme `U` locally of finite type over `S`, and `x₀` an object of
`𝒳` over a field `k` of finite type over `S`. This file proves that the tangent space of the
deformation category `𝓕_{𝒳,k,x₀}` of Tag 07T2 is finite dimensional over `k`.

The proof follows Tag 07X1. The presentation is smooth on predeformation categories (Tag 07WK,
case (3), whose input from Tag 04AM is
`AlgebraicGeometry.Space.formallySmooth_of_isSmooth_unconditional`). Choose a finite separable
extension `l / k` and a point `u₀` of `U` over `l` lifting `x₀`. Then
`T𝓕 ⊗_k l ≅ T𝓕_{l/k}` (Tag 07WB), the canonical functor `𝓕_{l/k} ⟶ 𝓕_{𝒳,l,x_{l,0}}` of Tag 07WX
is full, so its differential is injective, and the differential of the smooth functor
`𝓕_{(Sch/U),l,u₀} ⟶ 𝓕_{𝒳,l,x_{l,0}}` is surjective (Tag 06HN, Tag 0DYP) out of the tangent space
of a point of a scheme locally of finite type, which is finite dimensional.

## Main results

* `Deformation.Artin.finiteDimensional_artinianTangentSpace_of_isAlgebraicStack`: the tangent
  space of `𝓕_{𝒳,k,x₀}` is finite dimensional.
* `Deformation.Artin.exists_chartPoint`: a point of the presentation over a finite extension
  of `k` lifting `x₀`.
* `Deformation.Artin.finiteDimensional_artinianTangentSpace_of_chartPoint`: the tangent space
  is finite dimensional given such a point.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isSmooth`: a smooth 1-morphism from a
  scheme to an algebraic stack is smooth on predeformation categories.
* `Deformation.differential_injective_of_full`: the differential of a full morphism of
  predeformation categories is injective.
* `Deformation.finiteDimensional_artinianTangentSpace_of_isSmooth`,
  `Deformation.finiteDimensional_artinianTangentSpace_of_full_changeOfFields`: finite
  dimensionality of tangent spaces is pushed forward along smooth morphisms and descends along
  full change-of-fields functors.

## References

* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 07WB](https://stacks.math.columbia.edu/tag/07WB)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w v z y z₂ y₂ u₁ v₁ u₂ v₂

namespace Deformation

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The differential of a full morphism of predeformation categories is injective.** Two
objects over the dual numbers whose images are isomorphic over the identity are isomorphic: the
isomorphism lifts by fullness to a morphism lying over the identity, which is an isomorphism
because the source is cofibered in groupoids. -/
theorem differential_injective_of_full
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.Full] :
    Function.Injective (differential h𝓕 h𝓖 φ) := by
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  intro z z' h
  obtain ⟨x, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z
  obtain ⟨x', rfl⟩ := classOf_surjective 𝓕 h𝓕 A z'
  change mapIsomorphismClasses h𝓕 h𝓖 φ A (classOf 𝓕 h𝓕 x) =
    mapIsomorphismClasses h𝓕 h𝓖 φ A (classOf 𝓕 h𝓕 x') at h
  rw [mapIsomorphismClasses_classOf, mapIsomorphismClasses_classOf] at h
  have hq := congrArg (cast (isomorphismClasses_obj 𝓖 h𝓖 A)) h
  rw [classOf_eq, classOf_eq] at hq
  obtain ⟨e⟩ := Quotient.exact hq
  -- lift the isomorphism of images by fullness
  let χ : x.1 ⟶ x'.1 := φ.toFunctor.preimage e.hom.1
  have hχ : φ.toFunctor.map χ = e.hom.1 := φ.toFunctor.map_preimage _
  have hlift : 𝓕.p.IsHomLift (𝟙 A) χ := by
    have he : 𝓖.p.IsHomLift (𝟙 A) e.hom.1 := e.hom.2
    rw [← hχ] at he
    exact @BasedFunctor.isHomLift_map _ _ _ _ φ _ _ _ _ (𝟙 A) χ he
  have : IsIso (𝓕.p.map χ) := by
    rw [IsHomLift.fac' 𝓕.p (𝟙 A) χ]
    infer_instance
  have : IsIso χ := isIso_of_isIso_map h𝓕 χ
  apply classOf_eq_of_isIsomorphic
  exact ⟨⟨Functor.Fiber.homMk 𝓕.p A χ, Functor.Fiber.homMk 𝓕.p A (inv χ),
    Functor.Fiber.hom_ext (IsIso.hom_inv_id χ), Functor.Fiber.hom_ext (IsIso.inv_hom_id χ)⟩⟩

/-- **A smooth morphism of deformation categories has finite dimensional target tangent space
when its source has one.** The differential is surjective (Tag 0DYP) and linear (Tag 06IJ). -/
theorem finiteDimensional_artinianTangentSpace_of_isSmooth
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsDeformationCategory 𝓕.p) (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (hφ : IsSmooth φ)
    (h : letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) :=
        ⟨tangentConditionS2 h𝓕⟩
      FiniteDimensional k
        (artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) :=
      ⟨tangentConditionS2 h𝓖⟩
    FiniteDimensional k
      (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) :=
    ⟨tangentConditionS2 h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) :=
    ⟨tangentConditionS2 h𝓖⟩
  exact Module.Finite.of_surjective
    (IsLinearMap.mk' _ (differential_isLinearMap 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation
      (tangentConditionS2 h𝓕) (tangentConditionS2 h𝓖) φ))
    ((isSmooth_iff_differential_surjective_and_lifts h𝓕 h𝓖 φ).1 hφ).1

end

/-- **Finite dimensionality descends along a full change-of-fields functor.** Let `l / k` be a
finite extension. If the functor from the category `𝓕_{l/k}` of Tag 07W9 to a predeformation
category `𝓗` over `𝒞_{Λ,l}` is full, and the tangent space of `𝓗` is finite dimensional over
`l`, then the tangent space of `𝓕` is finite dimensional over `k`: by Tag 07WB the tangent
space of `𝓕_{l/k}` is `T𝓕 ⊗_k l`, and the differential of a full functor is injective and
`l`-linear (Tag 06IJ). -/
theorem finiteDimensional_artinianTangentSpace_of_full_changeOfFields
    (T : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} T.Λ T.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hp.cofibered)))
    (𝓗 : BasedCategory.{z₂, y₂} (ArtinianLocalAlgCat.{u, v, v} T.Λ T.l))
    (h𝓗 : IsPredeformationCategory 𝓗.p)
    (hS2𝓗 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓗 h𝓗.cofibered)))
    (G : BasedFunctor (⟨ChangeOfFieldsCategory T 𝓕.p, inferInstance,
      changeOfFieldsProjection T 𝓕.p⟩ :
        BasedCategory.{max v z, max (max u (v + 1)) y} (ArtinianLocalAlgCat.{u, v, v} T.Λ T.l))
      𝓗)
    [G.toFunctor.Full]
    (h : letI : Fact (IsPredeformationCategory 𝓗.p) := ⟨h𝓗⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓗 h𝓗.cofibered))) := ⟨hS2𝓗⟩
      FiniteDimensional T.l (artinianTangentSpace T.Λ T.l (isomorphismClasses 𝓗 h𝓗.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
    FiniteDimensional T.k (artinianTangentSpace T.Λ T.k (isomorphismClasses 𝓕 hp.cofibered)) := by
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} T.Λ T.l) :=
    ⟨ChangeOfFieldsCategory T 𝓕.p, inferInstance, changeOfFieldsProjection T 𝓕.p⟩
  let hq : IsPredeformationCategory 𝓖.p :=
    changeOfFieldsProjection_isPredeformationCategory T 𝓕.p hp
  have hS2' := associatedSchlessingerConditionS2_changeOfFields T 𝓕 hp hS2
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨hq⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 hq.cofibered))) := ⟨hS2'⟩
  let : Fact (IsPredeformationCategory 𝓗.p) := ⟨h𝓗⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓗 h𝓗.cofibered))) := ⟨hS2𝓗⟩
  let e := tangentSpaceChangeOfFields T 𝓕 hp hS2
  let L := (IsLinearMap.mk' _ (differential_isLinearMap 𝓖 𝓗 hq h𝓗 hS2' hS2𝓗 G)).comp e.toLinearMap
  have : Module.Finite T.l (TensorProduct T.k T.l
      (artinianTangentSpace T.Λ T.k (isomorphismClasses 𝓕 hp.cofibered))) :=
    Module.Finite.of_injective L
      ((differential_injective_of_full hq.cofibered h𝓗.cofibered G).comp e.injective)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat T.l

end Deformation

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth 1-morphism from a scheme to an algebraic stack is smooth on predeformation
categories.** This is case (3) of Tag 07WK at a presentation: the 1-morphism is representable
by algebraic spaces because the diagonal of an algebraic stack is (Tag 045G), it has the
relative smoothness property by Tag 06FM, and the implication from smoothness to formal
smoothness of Tag 04AM holds for morphisms of algebraic spaces. -/
theorem isSmoothOnPredeformationCategories_of_isSmooth [IsLocallyNoetherian S]
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a) :
    IsSmoothOnPredeformationCategories B S hS
      (Stack.schemeStack.{u, w} B S hS U).val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor a.hom) (CatFiberedInGroupoids.homFunctor_comp_p a.hom) := by
  have hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳.val :=
    Stack.SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    Stack.isRepresentableFromSchemes_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val
      ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).1 hdiag)
      U a.hom.hom
  have _ : (Stack.spaceProperty B S hS (fun _ _ h => Space.IsSmooth B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := inferInstance
  have hrel := (Stack.hasPropertyOnSomeSmoothDiagram_iff_relative B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (Stack.schemeStack.{u, w} B S hS U).property 𝒳.property a.hom hrep).1 hsm
  have hFS : ∀ {X Y : AlgebraicSpaces B S hS} (m : X ⟶ Y),
      Space.IsSmooth B S hS m.hom → Space.FormallySmooth m.hom :=
    fun {X Y} m hm => Space.formallySmooth_of_isSmooth_unconditional X.2 Y.2 m.hom hm
  intro Λ k _ _ _ iΛ x₀ hx₀ h1 h2 h3
  exact @isSmoothOnPredeformationCategories_of_isRelativelySmooth B S hS _
    _ _ a.hom ⟨hrep, hrel⟩ hFS Λ k _ _ _ iΛ x₀ hx₀ h1 h2 h3

/-- `Spec l ⟶ Spec k` is locally of finite type when `l` is a finite extension of `k`. -/
private theorem locallyOfFiniteType_spec_map_algebraMap_of_finite (k l : Type u) [Field k]
    [Field l] [Algebra k l] [Module.Finite k l] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k l))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.FiniteType.of_finite (RingHom.finite_algebraMap.mpr inferInstance))

/-- The point `Spec l ⟶ S` of a change of fields situation is of finite type over `S` when the
point `Spec k ⟶ S` is, `l` being finite over `k`. -/
theorem locallyOfFiniteType_quasiCompact_extendedPoint (T : ChangeOfFieldsSituation.{u, u, u})
    (iΛ : Spec (.of T.Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsScalarTower.algebraMap_apply T.Λ T.k T.l x
  have := locallyOfFiniteType_spec_map_algebraMap_of_finite T.k T.l
  have := hfinite
  have := hqc
  rw [e, Category.assoc]
  exact ⟨inferInstance, inferInstance⟩

/-- **The tangent space at a point lifting to a smooth presentation is finite dimensional.**
Let `l / k` be a finite extension, `u₀` a point over `l` of a scheme `U` locally of finite type
over `S`, and `η` an arrow from the image of `u₀` under a smooth 1-morphism `(Sch/U) ⟶ 𝒳` to
`x₀`, lying over `Spec l ⟶ Spec k`. Then the tangent space of `𝓕_{𝒳,k,x₀}` is finite
dimensional over `k`. -/
theorem finiteDimensional_artinianTangentSpace_of_chartPoint [IsLocallyNoetherian S]
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a)
    (T : ChangeOfFieldsSituation.{u, u, u}) (iΛ : Spec (.of T.Λ) ⟶ S) [IsOpenImmersion iΛ]
    (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (u₀ : Over U)
    (hu₀ : (Over.forget U ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hxₗ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj
        ((CatFiberedInGroupoids.homFunctor a.hom).obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (η : (CatFiberedInGroupoids.homFunctor a.hom).obj u₀ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((𝒳.val.val.p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l))) :
    let D := predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    let hD : IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ x₀ hx₀
        hfinite hqc
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p) :=
      ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered))) :=
      ⟨tangentConditionS2 hD⟩
    FiniteDimensional T.k (artinianTangentSpace T.Λ T.k (isomorphismClasses
      (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered)) := by
  intro D hD
  obtain ⟨hfinl, hqcl⟩ :=
    locallyOfFiniteType_quasiCompact_extendedPoint S T iΛ hfinite hqc
  let p := 𝒳.val.val.p
  let hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let F := CatFiberedInGroupoids.homFunctor a.hom
  let xₗ := F.obj u₀
  -- the deformation category at the point over `l`
  let Dₗ := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ
  let := Dₗ.category
  have hDₗ : IsDeformationCategory Dₗ.projection :=
    isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ xₗ hxₗ
      hfinl hqcl
  -- the change of fields functor is full
  have hη : p.IsCartesian (p.map η) η := by
    have := hp.isStronglyCartesian_homLift (p.map η) η
    infer_instance
  let G := Site.changeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
  have : G.toFunctor.IsEquivalence :=
    Site.changeOfFieldFunctor_isEquivalence T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
      ⟨hfinite, hqc⟩ (satisfiesRS_of_isAlgebraicStack B S hS 𝒳)
  let Gb : BasedFunctor (⟨ChangeOfFieldsCategory T (BasedCategory.ofFunctor D.projection).p,
      inferInstance, changeOfFieldsProjection T (BasedCategory.ofFunctor D.projection).p⟩ :
        BasedCategory (ArtinianLocalAlgCat.{u, u, u} T.Λ T.l))
      (BasedCategory.ofFunctor Dₗ.projection) :=
    { toFunctor := G.toFunctor
      w := G.projection_comm }
  have : Gb.toFunctor.Full := inferInstanceAs G.toFunctor.Full
  -- the presentation is smooth on deformation categories
  have hsmooth := isSmoothOnPredeformationCategories_of_isSmooth B S hS 𝒳 U a hsm
    iΛ u₀ hu₀ hfinl hqcl inferInstance
  have hU : IsDeformationCategory (SliceTangent.sliceBased iΛ u₀ hu₀).p :=
    SliceTangent.isDeformationCategory_sliceDeformations (iΛ := iΛ) (v₀ := u₀) (hv₀ := hu₀)
      hfinl hqcl
  have hfdU := SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased
    hU.predeformation (tangentConditionS2 hU)
  have hfdₗ := finiteDimensional_artinianTangentSpace_of_isSmooth hU hDₗ _ hsmooth hfdU
  exact finiteDimensional_artinianTangentSpace_of_full_changeOfFields T
    (BasedCategory.ofFunctor D.projection) hD.predeformation (tangentConditionS2 hD)
    (BasedCategory.ofFunctor Dₗ.projection) hDₗ.predeformation (tangentConditionS2 hDₗ) Gb hfdₗ

/-- The structure morphism of an object of a slice equal to `Over.mk f` is `f`, up to the
identification of the sources. -/
theorem over_hom_of_eq {C : Type*} [Category C] {Z Y : C} {X : Over Z} {f : Y ⟶ Z}
    (h : X = Over.mk f) : eqToHom (congrArg Comma.left h).symm ≫ X.hom = f := by
  subst h
  simp

/-- A morphism whose image is a given morphism followed by an identification lies over it. -/
theorem isHomLift_of_map_eq_comp_eqToHom {C D : Type*} [Category C] [Category D] (p : C ⥤ D)
    {a b : C} (φ : a ⟶ b) {R T T' : D} (f : R ⟶ T) (h : T = T') (e₁ : p.obj a = R)
    (e₂ : T' = p.obj b)
    (hφ : p.map φ = eqToHom e₁ ≫ (f ≫ eqToHom h) ≫ eqToHom e₂) : p.IsHomLift f φ := by
  refine IsHomLift.of_fac' p f φ e₁ (h.trans e₂).symm ?_
  rw [hφ]
  simp

/-- The morphism of schemes underlying an arrow of a category over the big site, read between
identified sources, is the morphism it lies over. -/
theorem postInclusion_map_left_eq_of_isHomLift {𝒳 : Type*} [Category 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {a b : 𝒳}
    {A A' : BigFppfOver B S hS} (g : A ⟶ A') (η : a ⟶ b) [p.IsHomLift g η]
    {Ya Yb : Scheme.{u}} {fa : Ya ⟶ S} {fb : Yb ⟶ S}
    (ha : (p ⋙ Over.post B.inclusion).obj a = Over.mk fa)
    (hb : (p ⋙ Over.post B.inclusion).obj b = Over.mk fb) :
    eqToHom (congrArg Comma.left ha).symm ≫ ((p ⋙ Over.post B.inclusion).map η).left ≫
        eqToHom (congrArg Comma.left hb) =
      eqToHom ((congrArg Comma.left ha).symm.trans
          (congrArg (fun X : BigFppfOver B S hS => B.inclusion.obj X.left)
            (IsHomLift.domain_eq p g η))) ≫
        B.inclusion.map g.left ≫
        eqToHom ((congrArg (fun X : BigFppfOver B S hS => B.inclusion.obj X.left)
            (IsHomLift.codomain_eq p g η)).symm.trans (congrArg Comma.left hb)) := by
  obtain rfl := IsHomLift.domain_eq p g η
  obtain rfl := IsHomLift.codomain_eq p g η
  obtain rfl := IsHomLift.eq_of_isHomLift p g η
  rfl

/-- **A point of a smooth surjective presentation over a finite extension.** Given a smooth
surjective 1-morphism `(Sch/U) ⟶ 𝒳` and an object `x₀` of `𝒳` over a field `k`, there are a
finite extension `l / k`, an object `u₀` of `(Sch/U)` over `Spec l`, and an arrow from its
image to `x₀` lying over `Spec l ⟶ Spec k`. The pullback of the presentation to `Spec k` is
smooth and surjective, so it has a point with values in a finite separable extension of `k`
(Tag 056U). -/
theorem exists_chartPoint (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsurj : Stack.IsSurjective B S hS a) (hsm : Stack.AlgebraicStacks.IsSmooth B S hS a)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l), Module.Finite k l ∧
      ∃ (u₀ : Over U) (_ : (Over.forget U ⋙ Over.post B.inclusion).obj u₀ =
          Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k))) ≫ iΛ))
        (hxₗ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj
            ((CatFiberedInGroupoids.homFunctor a.hom).obj u₀) =
          Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k))) ≫ iΛ))
        (η : (CatFiberedInGroupoids.homFunctor a.hom).obj u₀ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
          ((𝒳.val.val.p ⋙ Over.post B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) := by
  let p := 𝒳.val.val.p
  let F := CatFiberedInGroupoids.homFunctor a.hom
  let Xk : BigFppfOver B S hS := p.obj x₀
  obtain ⟨Tm, m, hm, hms, x, α, hα⟩ :=
    Stack.exists_scheme_lift_of_isSurjective_isSmooth B S hS a hsurj hsm Xk ⟨x₀, rfl⟩
  have hk : B.inclusion.obj Xk.left = Spec (.of k) := congrArg Over.left hx₀
  let m' : B.inclusion.obj Tm ⟶ Spec (.of k) := B.inclusion.map m ≫ eqToHom hk
  have : Smooth m' := by have := hm; infer_instance
  have : Surjective m' := by have := hms; infer_instance
  obtain ⟨l, _, _, hfin, -, pt, hpt⟩ := exists_finite_separable_point_of_smooth m'
  refine ⟨l, inferInstance, inferInstance, hfin, ?_⟩
  have hptm : pt ≫ B.inclusion.map m =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ eqToHom hk.symm := by
    rw [← hpt]
    simp [m']
  have := locallyOfFiniteType_spec_map_algebraMap_of_finite k l
  have : LocallyOfFiniteType (pt ≫ B.inclusion.map m) := by
    rw [hptm]
    infer_instance
  have hcont : B.Contains (Spec (.of l)) :=
    contains_of_locallyOfFiniteType B (U := Xk.left) (pt ≫ B.inclusion.map m)
  let Tobj : BigFppfOver B S hS := Over.mk (m ≫ Xk.hom)
  let L : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (P := B.Contains) (X := B.obj hcont) pt ≫ Tobj.hom)
  let gL : L ⟶ Tobj := Over.homMk (ObjectProperty.homMk pt) rfl
  have hFp := CatFiberedInGroupoids.homFunctor_comp_p a.hom
  have := hα
  have hxleft : (Over.forget U).obj x = Tobj :=
    (Functor.congr_obj hFp x).symm.trans (IsHomLift.domain_eq p (Over.homMk m rfl) α)
  let u₀ : Over U := Over.mk (gL ≫ eqToHom hxleft.symm ≫ x.hom)
  let hu : u₀ ⟶ x := Over.homMk (gL ≫ eqToHom hxleft.symm) (by simp [u₀])
  have hXk : eqToHom hk.symm ≫ B.inclusion.map Xk.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ :=
    over_hom_of_eq hx₀
  have hu₀ : (Over.forget U ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k))) ≫ iΛ) := by
    show Over.mk (B.inclusion.map L.hom) = _
    congr 1
    show pt ≫ B.inclusion.map m ≫ B.inclusion.map Xk.hom = _
    rw [← Category.assoc, hptm, Category.assoc, hXk, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hxₗ : (p ⋙ Over.post B.inclusion).obj (F.obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k))) ≫ iΛ) :=
    (congrArg (Over.post B.inclusion).obj (Functor.congr_obj hFp u₀)).trans hu₀
  refine ⟨u₀, hu₀, hxₗ, F.map hu ≫ α, ?_⟩
  have h1 : 𝒳.val.val.p.map (F.map hu) = eqToHom (Functor.congr_obj hFp u₀) ≫
      (gL ≫ eqToHom hxleft.symm) ≫ eqToHom (Functor.congr_obj hFp x).symm :=
    Functor.congr_hom hFp hu
  have : 𝒳.val.val.p.IsHomLift gL (F.map hu) := isHomLift_of_map_eq_comp_eqToHom _ _ _ _ _ _ h1
  have : 𝒳.val.val.p.IsHomLift (gL ≫ (Over.homMk m rfl : Tobj ⟶ Xk)) (F.map hu ≫ α) :=
    inferInstance
  rw [postInclusion_map_left_eq_of_isHomLift B S hS 𝒳.val.val.p
    (gL ≫ (Over.homMk m rfl : Tobj ⟶ Xk)) (F.map hu ≫ α) hxₗ hx₀]
  show eqToHom _ ≫ (pt ≫ B.inclusion.map m) ≫ eqToHom _ = _
  rw [hptm]
  simp

/-- **The tangent space of the deformation category of a point of an algebraic stack is finite
dimensional** (the tangent space half of Tag 07X1), for the vector space structure of
Tag 06IH. -/
theorem finiteDimensional_artinianTangentSpace_of_isAlgebraicStack [IsLocallyNoetherian S]
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
    let hD : IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_isAlgebraicStack B S hS 𝒳 iΛ x₀ hx₀
        hfinite hqc
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p) :=
      ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered))) :=
      ⟨tangentConditionS2 hD⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses
      (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered)) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  obtain ⟨l, _, _, _, u₀, hu₀, hxₗ, η, hη⟩ := exists_chartPoint B S hS 𝒳 U a hsurj hsm iΛ x₀ hx₀
  let : Algebra Λ l := ((algebraMap k l).comp (algebraMap Λ k)).toAlgebra
  have : IsScalarTower Λ k l := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let T : ChangeOfFieldsSituation.{u, u, u} := ⟨Λ, k, l⟩
  exact finiteDimensional_artinianTangentSpace_of_chartPoint B S hS 𝒳 U a hsm T iΛ x₀ hx₀
    hfinite hqc u₀ hu₀ hxₗ η hη

end Deformation.Artin

end
